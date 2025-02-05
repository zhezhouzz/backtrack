module type Monad = sig
  type 'a m

  val return : 'a -> 'a m
  val ( >>= ) : 'a m -> ('a -> 'b m) -> 'b m
  val ( let* ) : 'a m -> ('a -> 'b m) -> 'b m
end

module type MonadPlus = sig
  include Monad

  val _0 : 'a m
  val ( #+ ) : 'a m -> 'a m -> 'a m
end

(** Laws for MonadPlus:
    a #+ _0 = a
    _0 #+ a = a
    a #+ b #+ c = a #+ (b #+ c)
    _0 >>= k = _0
    a #+ b >>= k = (a >>= k) #+ (b >>= k)
 **)

module type LogicT = sig
  include MonadPlus

  val msplit : 'a m -> ('a * 'a m) option m
  val ( #++ ) : 'a m -> 'a m -> 'a m
  val ( >>- ) : 'a m -> ('a -> 'b m) -> 'b m
  val ifte : 'a m -> ('a -> 'b m) -> 'b m -> 'b m
  val once : 'a m -> 'a m
end

module SFKT (M : Monad) : LogicT = struct
  type 'ans fk = unit -> 'ans
  (* Failure continuation, OCaml is a strict language thus we use a thunk. *)

  type ('ans, 'a) sk = 'a -> 'ans fk -> 'ans (* Success continuation *)
  type 'a m = { sfkt : 'ans. ('ans M.m, 'a) sk -> 'ans M.m fk -> 'ans M.m }

  let return (x : 'a) : 'a m = { sfkt = (fun sk fk -> sk x fk) }

  let ( >>= ) (x : 'a m) (f : 'a -> 'b m) : 'b m =
    { sfkt = (fun sk -> x.sfkt (fun x' -> (f x').sfkt sk)) }

  let ( let* ) = ( >>= )
  let _0 = { sfkt = (fun _ fk -> fk ()) }

  let ( #+ ) (x : 'a m) (y : 'a m) : 'a m =
    { sfkt = (fun sk fk -> x.sfkt sk (fun () -> y.sfkt sk fk)) }

  let lift (m : 'a M.m) : 'a m =
    { sfkt = (fun sk fk -> M.( >>= ) m (fun a -> sk a fk)) }

  let reflect (m : ('a * 'a m) option) : 'a m =
    match m with None -> _0 | Some (a, m') -> (return a) #+ m'

  let msplit (x : 'a m) : ('a * 'a m) option m =
    lift
      (x.sfkt
         (fun a fk -> M.return (Some (a, lift (fk ()) >>= reflect)))
         (fun () -> M.return None))

  let rec ( #++ ) (x : 'a m) (y : 'a m) : 'a m =
    let* (r : ('a * 'a m) option) = msplit x in
    match r with None -> y | Some (xhd, xtl) -> (return xhd) #+ (y #++ xtl)

  let rec ( >>- ) (x : 'a m) (f : 'a -> 'b m) : 'b m =
    let* (r : ('a * 'a m) option) = msplit x in
    match r with None -> _0 | Some (xhd, xtl) -> (f xhd) #++ (xtl >>- f)

  let ifte (cond : 'a m) (tl : 'a -> 'b m) (el : 'b m) : 'b m =
    let* (r : ('a * 'a m) option) = msplit cond in
    match r with None -> el | Some (xhd, xtl) -> (tl xhd) #+ (xtl >>= tl)

  let once (x : 'a m) : 'a m =
    let* (r : ('a * 'a m) option) = msplit x in
    match r with None -> _0 | Some (xhd, _) -> return xhd
end

let ( !$ ) = Lazy.force

module type STREAM = sig
  type 'a stream_cell = Nil | Cons of 'a * 'a stream
  and 'a stream = 'a stream_cell Lazy.t

  val empty : 'a stream
  val produce : 'a -> 'a stream -> 'a stream
  val ( ++ ) : 'a stream -> 'a stream -> 'a stream (* stream append *)
  val destruct : int -> 'a stream -> 'a list * 'a stream
  val take : int -> 'a stream -> 'a stream
  val drop : int -> 'a stream -> 'a stream
  val reverse : 'a stream -> 'a stream
  val concatmap : 'a stream -> ('a -> 'a stream) -> 'a stream
end

module Stream : STREAM = struct
  type 'a stream_cell = Nil | Cons of 'a * 'a stream
  and 'a stream = 'a stream_cell Lazy.t

  let empty = lazy Nil
  let produce a s = lazy (Cons (a, s))

  let rec ( ++ ) s1 s2 =
    lazy
      (match s1 with
      | (lazy Nil) -> !$s2
      | (lazy (Cons (hd, tl))) -> Cons (hd, tl ++ s2))

  let rec take n s =
    lazy
      (if n = 0 then Nil
       else
         match s with
         | (lazy Nil) -> Nil
         | (lazy (Cons (hd, tl))) -> Cons (hd, take (n - 1) tl))

  let rec drop n s =
    lazy
      (match (n, s) with
      | 0, _ -> !$s
      | _, (lazy Nil) -> Nil
      | _, (lazy (Cons (_, tl))) -> !$(drop (n - 1) tl))

  let rec destruct n s =
    match (n, s) with
    | 0, _ -> ([], s)
    | _, (lazy Nil) -> failwith "die"
    | _, (lazy (Cons (hd, tl))) ->
        let l, st = destruct (n - 1) tl in
        (hd :: l, st)

  let reverse s =
    let rec reverse' acc s =
      lazy
        (match s with
        | (lazy Nil) -> !$acc
        | (lazy (Cons (hd, tl))) -> !$(reverse' (lazy (Cons (hd, acc))) tl))
    in
    reverse' (lazy Nil) s

  let rec concatmap s f =
    lazy
      (match s with
      | (lazy Nil) -> Nil
      | (lazy (Cons (hd, tl))) -> !$(f hd ++ concatmap tl f))
end

module AE = struct
  open Effect
  open Effect.Deep

  type _ Effect.t +=
    | MReturn : int -> unit t
    | MBind : (int -> unit) -> unit t
    | MFairBind : (int -> unit) -> unit t
    | MZero : unit t
    | MPlus : (int -> unit) -> unit t
    | MInterleave : (int -> unit) -> unit t
    | MIfte : (int -> unit) * (int -> unit) -> unit t
    | MCut : (int -> unit) * (int -> unit) -> unit t
    | MOnce : unit t

  open Stream

  let rec handler (main : 'a -> unit) (input : 'a) : int stream_cell =
    match_with main input
      {
        retc = (fun _ -> Nil);
        exnc = raise;
        effc =
          (fun (type b) (e : b Effect.t) ->
            match e with
            | MReturn x ->
                Printf.printf "effect return %i!\n" x;
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    !$(produce x (lazy (continue k ()))))
            | MBind f ->
                Printf.printf "effect bind!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    !$(concatmap
                         (lazy (continue k ()))
                         (fun x -> lazy (handler f x))))
            | MFairBind f ->
                Printf.printf "effect bind!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    match continue k () with
                    | Nil -> Nil
                    | Cons (hd, tl) ->
                        !$(concatmap tl (fun x -> lazy (handler f x))
                          ++ lazy (handler f hd)))
            | MZero ->
                Printf.printf "effect zero!\n";
                Some (fun (_ : (b, int stream_cell) continuation) -> Nil)
            | MPlus (k' : int -> unit) ->
                Printf.printf "effect plus!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    !$(lazy (handler k' 0) ++ lazy (continue k ())))
            | MInterleave (k' : int -> unit) ->
                Printf.printf "effect return!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    match handler k' 0 with
                    | Nil -> continue k ()
                    | Cons (hd, tl) -> Cons (hd, lazy (continue k ()) ++ tl))
            | MIfte (sk, fk) ->
                Printf.printf "effect return!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    match continue k () with
                    | Nil -> handler fk 0
                    | Cons (hd, tl) ->
                        !$(concatmap
                             (lazy (Cons (hd, tl)))
                             (fun x -> lazy (handler sk x))))
            | MCut (sk, fk) ->
                Printf.printf "effect return!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    match continue k () with
                    | Nil -> handler fk 0
                    | Cons (hd, _) -> !$(lazy (handler sk hd)))
            | MOnce ->
                Printf.printf "effect return!\n";
                Some
                  (fun (k : (b, int stream_cell) continuation) ->
                    match continue k () with
                    | Nil -> Nil
                    | Cons (hd, _) -> Cons (hd, empty))
            | _ -> None);
      }

  let return x = perform (MReturn x)
  let returnC x _ = perform (MReturn x)
  let bind f = perform (MBind f)
  let mplus y = perform (MPlus y)
  let minterleave y = perform (MInterleave y)
  let ifte succ fail = perform (MIfte (succ, fail))
  let cut succ fail = perform (MCut (succ, fail))
  let failure _ = perform MZero
  let once () = perform MOnce

  let rec odds _ =
    mplus (returnC 1);
    bind (fun x -> return (2 + x));
    odds 0

  let rec iota (n : int) =
    if n <= 1 then return 1
    else (
      mplus (returnC n);
      iota (n - 1))

  let prime _ =
    bind (fun n ->
        if n > 1 then (
          ifte failure (returnC n);
          bind (fun d -> if d > 1 && n mod d == 0 then return d else failure ());
          iota (n - 1))
        else failure ());
    odds 0
end

let test_odds () =
  let stream = lazy (AE.handler AE.odds 0) in
  let l, _ = Stream.destruct 8 stream in
  List.iter (fun x -> Printf.printf "odds: %i\n" x) l

let test_iota () =
  let stream = lazy (AE.handler AE.iota 10) in
  let l, _ = Stream.destruct 8 stream in
  List.iter (fun x -> Printf.printf "random: %i\n" x) l

let test_prime () =
  let stream = lazy (AE.handler AE.prime 0) in
  let l, _ = Stream.destruct 20 stream in
  List.iter (fun x -> Printf.printf "prime: %i\n" x) l
