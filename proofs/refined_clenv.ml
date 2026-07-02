(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let subst_meta sigma s c =
  let rec subst c =
    match EConstr.kind sigma c with
    | Meta mv ->
      begin match Int.Map.find_opt mv s with
      | Some ev -> ev
      | None -> c
      end
    | _ -> EConstr.map sigma subst c
  in
  subst c

type meta_evar = {
  meta : Constr.metavariable;
  evar : Evar.t;
}

type current_meta_evar = {
  cmeta : Constr.metavariable;
  cevar : Evar.t;
}

let dest_evar sigma c =
  match EConstr.kind sigma c with
  | Evar (evk, _) -> evk
  | _ -> assert false

let replace_clenv_metas env sigma clenv =
  let module Metas = Unification.Meta in
  let metas = Clenv.clenv_meta_list clenv in
  let fold (sigma, metamap, evars) mv =
    match Metas.meta_opt_fvalue metas mv with
    | Some v ->
      let value = subst_meta sigma metamap v.rebus in
      sigma, Int.Map.add mv value metamap, evars
    | None ->
      let tymeta = Metas.meta_ftype metas mv in
      let ty = subst_meta sigma metamap tymeta.rebus in
      let ty = Reductionops.nf_betaiota env sigma ty in
      let src = Metas.evar_source_of_meta mv metas in
      let naming = match Metas.meta_name metas mv with
        | Name na -> Namegen.IntroIdentifier na
        | Anonymous -> Namegen.IntroAnonymous
      in
      let typeclass_candidate = Typeclasses.is_maybe_class_type env sigma ty in
      let sigma, term =
        Evarutil.new_evar ~src ~naming ~typeclass_candidate env sigma ty
      in
      let evar = dest_evar sigma term in
      sigma, Int.Map.add mv term metamap, { meta = mv; evar } :: evars
  in
  let sigma, metamap, evars =
    List.fold_left fold (sigma, Int.Map.empty, []) (Clenv.clenv_arguments clenv)
  in
  sigma, subst_meta sigma metamap, List.rev evars

let meta_evar_set evars =
  List.fold_left
    (fun accu { evar; _ } -> Evar.Set.add evar accu)
    Evar.Set.empty evars

let advance_meta_evars sigma evars =
  List.filter_map (fun { meta; evar } ->
    match Evarutil.advance sigma evar with
    | Some cevar -> Some { cmeta = meta; cevar }
    | None -> None)
    evars

let current_evar_set evars =
  List.fold_left
    (fun accu { cevar; _ } -> Evar.Set.add cevar accu)
    Evar.Set.empty evars

(* Like [Evd.evars_of_term], but without unfolding defined evars.  For
   deciding which clenv evars correspond to actual subgoals, we want the
   syntactic dependencies of the clause after evarconv, not dependencies hidden
   behind assignments made to unrelated evars during goal unification. *)
let evars_of_term c =
  let rec evrec acc c =
    match Constr.kind c with
    | Evar (evk, args) ->
      Evar.Set.add evk (SList.Skip.fold evrec acc args)
    | _ -> Constr.fold evrec acc c
  in
  evrec Evar.Set.empty (EConstr.Unsafe.to_constr c)

let evar_deps sigma current_set evk =
  let evi = Evd.find_undefined sigma evk in
  Evar.Set.inter current_set (evars_of_term (Evd.evar_concl evi))

let evar_deps_list sigma current_set evars =
  List.fold_left
    (fun deps { cevar; _ } -> Evar.Set.union deps (evar_deps sigma current_set cevar))
    Evar.Set.empty evars

let close_evar_deps sigma current_set seeds =
  let rec loop seen todo =
    match todo with
    | [] -> seen
    | evk :: todo ->
      let deps = Evar.Set.diff (evar_deps sigma current_set evk) seen in
      let seen = Evar.Set.union seen deps in
      loop seen (Evar.Set.elements deps @ todo)
  in
  loop seeds (Evar.Set.elements seeds)

(* A clenv meta should become a proofview goal when it corresponds to an
   ordinary argument of the applied hint, or when it is an actual typeclass
   goal.  Non-class evars that only parameterize such goals must remain
   evars: typeclass search can instantiate them when solving the goal they
   parameterize, and exposing them as goals leads to spurious searches such as
   goals of type [Type] or [relation A]. *)
let classify_evars env sigma typ value evars =
  let current = advance_meta_evars sigma evars in
  let current_set = current_evar_set current in
  let value_set = Evar.Set.inter current_set (evars_of_term value) in
  let deps = Evar.Set.inter current_set (evars_of_term typ) in
  let deps = Evar.Set.union deps (evar_deps_list sigma current_set current) in
  let goals =
    List.filter (fun { cevar; _ } ->
      let evi = Evd.find_undefined sigma cevar in
      Typeclasses.is_class_evar env sigma evi ||
      (Evar.Set.mem cevar value_set && not (Evar.Set.mem cevar deps)))
      current
  in
  let goal_set = current_evar_set goals in
  let protected = close_evar_deps sigma current_set goal_set in
  let unresolved =
    List.filter (fun { cevar; _ } ->
      Evar.Set.mem cevar value_set &&
      not (Evar.Set.mem cevar protected))
      current
  in
  goals, unresolved

let normalize_meta_evar_info sigma evars =
  let current = advance_meta_evars sigma evars in
  let current_set = current_evar_set current in
  Evd.raw_map_undefined (fun evk evi ->
    if Evar.Set.mem evk current_set then Evarutil.nf_evar_info sigma evi
    else evi)
    sigma

let normalize_evar_concl env sigma evk =
  let evi = Evd.find_undefined sigma evk in
  let env = Evd.evar_env env evi in
  let concl = Reductionops.nf_betaiota env sigma (Evd.evar_concl evi) in
  Evd.downcast evk concl sigma

let evarconv_flags ~allowed_evars flags =
  let open Unification in
  let core = flags.core_unify_flags in
  let subterm = flags.subterm_unify_flags in
  let closed_ts = match core.modulo_conv_on_closed_terms with
  | Some ts -> ts
  | None -> core.modulo_delta_types
  in
  { Evarsolve.modulo_betaiota = core.modulo_betaiota;
    open_ts = core.modulo_delta;
    closed_ts;
    subterm_ts = subterm.modulo_delta;
    allowed_evars;
    with_cs = true;
  }

let dft = Unification.default_unify_flags

let res_pf ?(with_evars=false) ?(with_classes=true) ?(flags=dft ()) clenv =
  Proofview.Goal.enter begin fun gl ->
    let env = Proofview.Goal.env gl in
    let concl = Proofview.Goal.concl gl in
    let metas = Clenv.clenv_meta_list clenv in
    let sigma, subst, evars =
      replace_clenv_metas env (Clenv.clenv_evd clenv) clenv
    in
    let meta_evars = meta_evar_set evars in
    let allowed_evars =
      let allowed = flags.Unification.core_unify_flags.Unification.allowed_evars in
      Evarsolve.AllowedEvars.from_pred (fun evk ->
        Evar.Set.mem evk meta_evars || Evarsolve.AllowedEvars.mem allowed evk)
    in
    let typ = subst (Clenv.clenv_type clenv) in
    let value = subst (Clenv.clenv_value clenv) in
    let sigma =
      Evarconv.unify ~flags:(evarconv_flags ~allowed_evars flags)
        env sigma Conversion.CUMUL typ concl
    in
    let sigma = normalize_meta_evar_info sigma evars in
    let independent, dependent = classify_evars env sigma typ value evars in
    let () =
      if not with_evars && not (List.is_empty dependent) then
        let missing =
          List.map (fun { cmeta; _ } -> Unification.Meta.meta_name metas cmeta) dependent
        in
        raise (Logic.RefinerError (env, sigma, Logic.UnresolvedBindings missing))
    in
    let sigma =
      if with_classes then
        let independent_evars = current_evar_set independent in
        let filter evk src =
          not (Evar.Set.mem evk independent_evars) && Typeclasses.all_evars evk src
        in
        let sigma =
          Typeclasses.resolve_typeclasses ~filter ~fail:(not with_evars) env sigma
        in
        (* After an apply, all the subgoals including those dependent shelved ones are in
           the hands of the user and resolution won't be called implicitely on them. *)
        Typeclasses.make_unresolvables (fun _ -> true) sigma
      else sigma
    in
    let independent_evars =
      List.filter_map (fun { cevar; _ } -> Evarutil.advance sigma cevar) independent
    in
    let sigma = List.fold_left (normalize_evar_concl env) sigma independent_evars in
    let sigma = List.fold_left Evd.remove_future_goal sigma independent_evars in
    Proofview.tclTHEN (Proofview.Unsafe.tclEVARS sigma) @@
    Refine.refine ~typecheck:true begin fun sigma ->
      let sigma =
        List.fold_left
          (fun sigma evk -> Evd.declare_future_goal evk sigma)
          sigma independent_evars
      in
      sigma, value
    end
  end
