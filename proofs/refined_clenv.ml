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

let classify_evars sigma typ value evars =
  let current = advance_meta_evars sigma evars in
  let current_set = current_evar_set current in
  let value_set = Evar.Set.inter current_set (Evd.evars_of_term sigma value) in
  let deps = Evar.Set.inter current_set (Evd.evars_of_term sigma typ) in
  let deps =
    List.fold_left (fun deps { cevar; _ } ->
      let evi = Evd.find_undefined sigma cevar in
      let evars = Evd.evars_of_term sigma (Evd.evar_concl evi) in
      Evar.Set.union deps (Evar.Set.inter current_set evars))
      deps current
  in
  List.partition (fun { cevar; _ } ->
    Evar.Set.mem cevar value_set && not (Evar.Set.mem cevar deps))
    current

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
    let independent, dependent = classify_evars sigma typ value evars in
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
