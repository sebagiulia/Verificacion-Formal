module Clase04.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  = match l1 with
    | [] -> ()
    | x::xs' -> sum_append xs' l2
              

(* Idem para length, definida en la librería de F*. *)
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  = match l1 with
    | [] -> ()
    | x::xs' -> len_append xs' l2
    
let rec snoc (xs : list int) (x : int) : list int =
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

let rec sublemma1 (xs ys : list int) (x : int)
  : Lemma (snoc (ys @ xs) x == ys @ snoc xs x) =
  match ys with
    | [] -> ()
    | y::ys' -> sublemma1 xs ys' x 

(*
    rev_int (x:xs @ ys) = rev_int (x::(xs' @ ys))
    = snoc x (rev_int (xs' @ ys)) H.I
    = snoc x (rev_int ys @ rev_int xs')
    = rev_int ys @ snoc x (rev_int xs') <-Sublemma1
    = rev_int ys @ rev_int (x::xs') 
*)

let rec rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs)
= match xs with
  | [] -> ()
  | x::xs' -> rev_append_int xs' ys;
              sublemma1 (rev_int xs') (rev_int ys) x
              


let rec sublemma2 (xs : list int) (x : int)
  : Lemma (rev_int (snoc xs x) == x::(rev_int xs)) = 
  match xs with
    | [] -> ()
    | y::ys' -> sublemma2 ys' x

(*
rev_int (rev_int x::xs)
= rev_int (snoc (rev_int xs) x) Sublemma2
= x :: rev_int (rev_int xs) H.I
= x :: xs
*)

let rec rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
= match xs with
  | [] -> ()
  | x::xs' -> rev_rev xs';
              sublemma2 (rev_int xs') x


(*
  rev_int xs == rev_int ys
  => rev_int (rev_int xs) == rev_int (rev_int ys)
  => xs == ys
*)

let rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
= rev_rev xs;
  rev_rev ys;
  ()
