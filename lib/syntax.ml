module type EXP = sig
  type value [@@deriving show, eq]
  type operator [@@deriving show, eq]

  type exp = Lit of value | Opr of { op : operator; arg1 : exp; arg2 : exp }
  [@@deriving show, eq]

  val to_value : exp -> value

  type potential_redex = Pr of { op : operator; varg1 : value; varg2 : value }
  [@@deriving show, eq]

  val contract : potential_redex -> exp
  (** We don't really care how contract are implemented. *)

  type decompose = exp -> potential_redex
  (** Decompose *)

  type recompose = exp -> exp
  (** Recompose, or evaluation context *)

  val small_step : show_step:(int -> exp -> unit) -> exp -> unit
end

module ExplicitSmallStep (Exp : EXP) = struct
  open Exp

  type intermidate = InterExp of exp | InterPr of potential_redex

  let intermidate_to_exp = function
    | InterExp e -> e
    | InterPr (Pr { op; varg1; varg2 }) ->
        Opr { op; arg1 = Lit varg1; arg2 = Lit varg2 }

  let rec mk_evaluation_ctx (e : exp) : intermidate * recompose =
    match e with
    | Lit _ -> (InterExp e, fun e -> e)
    | Opr { op; arg1; arg2 } -> (
        match (mk_evaluation_ctx arg1, mk_evaluation_ctx arg2) with
        | (InterExp arg1, _), (InterExp arg2, _) ->
            ( InterPr (Pr { op; varg1 = to_value arg1; varg2 = to_value arg2 }),
              fun e -> e )
        | (InterExp arg1, _), (InterPr pr, recompose2) ->
            (InterPr pr, fun e -> Opr { op; arg1; arg2 = recompose2 e })
        | (InterPr pr, recompose1), _ ->
            (InterPr pr, fun e -> Opr { op; arg1 = recompose1 e; arg2 }))

  let reduction (small_step : exp -> exp option) =
    let rec loop e =
      match small_step e with
      | Some e' ->
          Printf.printf "--> %s\n" (show_exp e');
          loop e
      | None -> Printf.printf "halt on %s\n" (show_exp e)
    in
    loop

  let small_step ~show_step (e : exp) =
    let rec loop (i, e) =
      show_step i e;
      match mk_evaluation_ctx e with
      | InterExp _, _ -> ()
      | InterPr pr, recompose ->
          let decompose _ = pr in
          loop (i + 1, recompose @@ contract @@ decompose e)
    in
    loop (0, e)

  let refocuing_small_step ~show_step (e : exp) =
    let rec loop i (inter, recomppse) =
      show_step i (intermidate_to_exp inter);
      match inter with
      | InterExp _ -> ()
      | InterPr pr ->
          let pr', recomppse' = mk_evaluation_ctx (contract pr) in
          loop (i + 1) (pr', fun e -> recomppse @@ recomppse' e)
    in
    loop 0 (mk_evaluation_ctx e)
end
