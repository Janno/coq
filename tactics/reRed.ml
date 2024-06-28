module ReductionBehaviour = Reductionops.ReductionBehaviour

let dbg = CDebug.create ~name:"rered" ()

(* Just like [CClosure.contract_fix_vect] but optionally uses [odef] for
   recursive occurrences of [fix]. *)
let contract_fix_vect odef fix =
  let open CClosure in
  let (thisbody, make_body, env, nfix) =
    match [@ocaml.warning "-4"] fix with
      | FFix (((reci,i),(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j ->
              let f =
                if j = i then
                  Option.default (FFix (((reci,j),rdcl), env)) odef
                else
                  (FFix (((reci,j),rdcl), env))
              in
              mk_red f
           ),
           env, Array.length bds)
      | FCoFix ((i,(_,_,bds as rdcl)),env) ->
          (bds.(i),
           (fun j -> mk_red (FCoFix ((j,rdcl),env))),
           env, Array.length bds)
      | _ -> assert false
  in
  let rec mk_subs env i =
    if Int.equal i nfix then env
    else mk_subs (Esubst.subs_cons (make_body i) env) (i + 1)
  in
  (Util.on_fst (fun env -> mk_subs env 0) env, thisbody)

let wh reds env sigma c =
  (* We are removing [fDELTA] and [fFIX] because those we need to handle manually *)
  let ccreds =
    RedFlags.(mkflags (List.filter (fun k -> red_set reds k) [fBETA;fMATCH;fCOFIX;fZETA]))
  in
  (* TODO: do we need to disable sharing if we don't set fDELTA anyway? If we
     bypass delta entirely we don't care about sharing. If we use the kernel to
     perform delta (as an extra step; the flag will always be disabled) then the
     cache might actually be helpful. *)
  let env = Environ.(set_typing_flags Declarations.{ (typing_flags env) with share_reduction = false }) env in
  let ccinfos = CClosure.create_clos_infos ccreds env in
  let cctab = CClosure.create_tab () in

  let luinfos = CClosure.create_clos_infos reds env in
  let lutab = CClosure.create_tab () in

  let ts = RedFlags.red_transparent reds in

  let use_fix = RedFlags.(red_set reds fFIX) in

  let red = CClosure.whd_stack ccinfos cctab in

  let find_fix refs fix =
    (* try to find a matching fixpoint in [refs] *)
    let fn ((_, _) as fix', _) =
      fix = fix'
      (* Array.for_all2 Int.equal recargs recargs' && *)
      (* i = i' *)
    in
    List.find_opt fn refs
  in

  let rec go refs ((fc, stack) : CClosure.fconstr * CClosure.stack_member list) =
    let ft = CClosure.fterm_of fc in
    match ft with
    (* Finished cases *)
    | CClosure.FRel _
    | CClosure.FAtom _
    | CClosure.FInd _
    | CClosure.FFix (_, _)
    | CClosure.FCoFix (_, _)
    | CClosure.FEvar (_, _, _, _)
    | CClosure.FInt _
    | CClosure.FFloat _
    | CClosure.FString _
    | CClosure.FArray (_, _, _)
    | CClosure.FLambda (_, _, _, _)
    | CClosure.FProd (_, _, _, _)
    | CClosure.FLetIn (_, _, _, _, _)
    | CClosure.FFlex (Names.RelKey _)
    | CClosure.FFlex (Names.VarKey _)
      ->
      (fc, stack)
    | CClosure.FProj (proj, _, _) when not (Names.PRpred.mem (Names.Projection.repr proj) ts.tr_prj)
      ->
      (fc, stack)
    | CClosure.FFlex (Names.ConstKey (cnst, _)) when not (Names.Cpred.mem cnst ts.tr_cst)
      ->
      (fc, stack)
    (* Impossible cases *)
    | CClosure.FApp (_, _)
      -> assert false
    | CClosure.FCaseT (_, _, _, _, _, _, _)
      -> assert false
    | CClosure.FCaseInvert (_, _, _, _, _, _, _, _)
      -> assert false
    | CClosure.FLIFT (_, _)
      -> assert false
    | CClosure.FLOCKED
      -> assert false
    | CClosure.FIrrelevant      (* impossible in reduction mode *)
      -> assert false
    (* Interesting cases *)
    | CClosure.FConstruct (c, usubs) ->
      begin
        let open CClosure in
        match [@ocaml.warning "-4"] strip_update_shift_app fc stack with
        | (_, cargs, Zfix(fx,par)::s) when use_fix ->
          let (fix, e) = match fterm_of fx with | FFix (fix, e) -> (fix, e) | _ -> assert false in
          let ofix =
            match find_fix refs fix with
            | Some (_, (cnst, univs)) when Esubst.is_subs_id (fst e) ->
              Some (FFlex (Names.ConstKey (cnst, univs)))
            | _ -> None
          in
          let rarg = zip fc cargs in
          let stack = par @ append_stack [|rarg|] s in
          let (fxe,fxbd) = contract_fix_vect ofix (fterm_of fx) in
          go refs (red (mk_clos fxe fxbd) stack)
        | (_,args,s) ->
          (fc, (args @ s))
      end
    | CClosure.FCLOS (fix, usubs) when Constr.isFix fix ->
      begin
        let (_,_) as fix = Constr.destFix fix in
        match find_fix refs fix with
        | Some (_, (cnst, univs)) when Esubst.is_subs_id (fst usubs) ->
          dbg Pp.(fun () -> str "refolding: " ++ Printer.pr_constant env cnst);
          let univs = CClosure.usubst_instance usubs univs in
          let fc = CClosure.mk_atom (Constr.mkConstU (cnst, univs)) in
          (fc, stack)
        | _ -> (fc, stack)
      end
    | CClosure.FCLOS (case, usubs) when Constr.isCase case ->
      assert false
    | CClosure.FCLOS _ ->
      assert false
    | CClosure.FFlex (Names.ConstKey (cnst, _ as cref) as key) ->
      dbg (fun () -> Printer.pr_constant env cnst);
      begin
        let open ReductionBehaviour in
        match get cnst with
        | None ->
          begin
            match CClosure.unfold_ref_with_args luinfos lutab key stack with
            | None -> (fc, stack)
            | Some (fc, stack) ->
              let refs =
                match CClosure.fterm_of fc with
                | CClosure.FCLOS (fix, _) when Constr.isFix fix ->
                  let fix = Constr.destFix fix in
                  (fix, cref) :: refs
                | _ -> refs
              in
              let r = red fc stack in
              go refs r
          end
        | Some NeverUnfold ->
          (fc, stack)
        | Some (UnfoldWhen {recargs;nargs}) ->
          if Option.compare Int.compare nargs (Some (CClosure.stack_args_size stack)) < 0 then
            (fc,stack)
          else
          begin
            match CClosure.get_nth_arg fc (List.hd recargs) stack with
            | (Some(pars,arg),stack) ->
              (* let (arg, arg_stack) = go refs (arg, pars) in *)
              (* if List.length arg_stack > 0 then (\*  *\) *)
              assert false
            | (None, stack) ->
              assert false
          end
        | Some UnfoldWhenNoMatch{recargs;nargs} ->
          assert false
      end
    | CClosure.FProj (_, _, _) ->
      (fc, stack)
  in
  let c = EConstr.Unsafe.to_constr c in
  let process = red CClosure.(mk_clos (Esubst.subs_id 0, UVars.Instance.empty) c) [] in
  let (fc, stack) = go [] process in
  let c = CClosure.term_of_process fc stack in
  EConstr.of_constr c

let rered (s : Genredexpr.strength) reds env sigma c =
  assert (s = Genredexpr.Head);
  wh reds env sigma c
