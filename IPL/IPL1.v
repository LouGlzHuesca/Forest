(********)
(*

Intuitionistic propositional logic using the RNmatrix described in:

LEME, Renato; CONIGLIO, Marcelo; LOPES, Bruno. Intuitionism with Truth Tables: A Decision Procedure for IPC Based on RNMatrix. arXiv preprint arXiv:2308.13664, 2023.

*)

(* Please note that, in this implementation, atomic propositions are defined using
natural numbers (see definition of iLF, below). *)
(****)

Require Import iLF.
Add LoadPath "../" as Main.
Require Import Main.Forest.
Require Import String.
Require Import List.
Import ListNotations.

Definition vF := 0. (* F *)
Definition vU := 1. (* U *)
Definition vT := 2. (* T *)

(* Auxiliary functions *)

Fixpoint unary_op
  (A B : iLF)
  (partialV : btree iLF)
  (vB : nat)
  (V : iLF -> nat -> btree iLF)
  : btree iLF
  :=
  match partialV with
  | Leaf _ _ =>
      V A vB
  | Alpha _ n t =>
      match n with
      | Node _ i D =>
          if (eqb_ilf B D) then
            Alpha _ n (unary_op A B t i V)
          else Alpha _ n (unary_op A B t vB V)
      end
  | Beta _ t1 t2 =>
      Beta _
        (unary_op A B t1 vB V)
        (unary_op A B t2 vB V)
  end.

Fixpoint bin_op
  (A B C : iLF)
  (partialV : btree iLF)
  (vB vC : nat)
  (V : iLF -> nat -> nat -> btree iLF)
  : btree iLF
  :=
  match partialV with
  | Leaf _ _ =>
      V A vB vC
  | Alpha _ n t =>
      match n with
      | Node _ i D =>
          if (eqb_ilf B D) then
            if (eqb_ilf C D) then
              Alpha _ n (bin_op A B C t i i V)
            else
              Alpha _ n (bin_op A B C t i vC V)
          else
            if (eqb_ilf C D) then
              Alpha _ n (bin_op A B C t vB i V)
            else Alpha _ n (bin_op A B C t vB vC V)
      end
  | Beta _ t1 t2 =>
      Beta _
        (bin_op A B C t1 vB vC V)
        (bin_op A B C t2 vB vC V)
  end.

(* Truth-table definitions *)

Definition Int_conj_def
  (* [vA] /\ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Alpha _ (Node _ (vF) A) (Leaf _ true)
  | 2 =>
      match vC with
      | (0 | 1) =>
          Alpha _ (Node _ (vF) A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      end
  | _ => Leaf _ true
  end.

Definition Int_conj_def_optimal
  (* [vA] /\ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Alpha _ (Node _ (vF) A) (Leaf _ true)
  | 2 =>
      match vC with
      | (0 | 1) =>
          Alpha _ (Node _ (vF) A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ (vT) A) (Leaf _ true)
      end
  | _ => Leaf _ true
  end.

Definition Int_conj_def_dummy
  (* [vA] /\ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Beta _
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
  | 2 =>
      match vC with
      | (0 | 1) =>
          Beta _
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
      | _ =>
          Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      end
  | _ => Leaf _ true
  end.

(* Disjunction *)

Definition Int_disj_def
  (* [vA] \/ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      match vC with
      | 2 =>
          Alpha _ (Node _ (vT) A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ (vF) A) (Leaf _ true)
      end
  | 2 =>
      match vC with
      | (0 | 1) =>
          Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      | _ =>
          Alpha _ (Node _ (vT) A) (Leaf _ true)
      end
  | _ => Leaf _ true
  end.

Definition Int_disj_def_optimal
  (* [vA] \/ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      match vC with
      | 2 =>
          Alpha _ (Node _ (vT) A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ (vF) A) (Leaf _ true)
      end
  | 2 =>
      Alpha _ (Node _ (vT) A) (Leaf _ true)
  | _ => Leaf _ true
  end.

Definition Int_disj_def_dummy
  (* [vA] \/ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      match vC with
      | 2 =>
          Beta _
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      | _ =>
          Beta _
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
      end
  | 2 =>
      Beta _
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
  | _ => Leaf _ true
  end.

(* Implication *)

Definition Int_impl_def
  (* [vA] -> [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
  | 2 =>
      match vC with
      | (0 | 1)  =>
          (Alpha _ (Node _ (vF) A) (Leaf _ true))
      | _ =>
          Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      end
  | _ => Leaf _ true
  end.

Definition Int_impl_def_optimal
  (* [vA] -> [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      match vC with
      | 2 =>
          (Alpha _ (Node _ (vT) A) (Leaf _ true))
      | _ =>
          Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      end
  | 2 =>
      match vC with
      | (0 | 1)  =>
          (Alpha _ (Node _ (vF) A) (Leaf _ true))
      | _ =>
          (Alpha _ (Node _ (vT) A) (Leaf _ true))
      end
  | _ => Leaf _ true
  end.

Definition Int_impl_def_dummy
  (* [vA] -> [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
  | 2 =>
      match vC with
      | (0 | 1)  =>
          Beta _
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
            (Alpha _ (Node _ (vF) A) (Leaf _ true))
      | _ =>
          Beta _
            (Alpha _ (Node _ (vU) A) (Leaf _ true))
            (Alpha _ (Node _ (vT) A) (Leaf _ true))
      end
  | _ => Leaf _ true
  end.

(* Negation *)

Definition Int_neg_def
  (* ~ [vA] *)
  (A : iLF)
  (vB : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Beta _
        (Alpha _ (Node _ (vU) A) (Leaf _ true))
        (Alpha _ (Node _ (vT) A) (Leaf _ true))
  | 2 =>
      (Alpha _ (Node _ (vF) A) (Leaf _ true))
  | _ => Leaf _ true
  end.

Definition Int_neg_def_dummy
  (* ~ [vA] *)
  (A : iLF)
  (vB : nat)
  : btree iLF
  :=
  match vB with
  | (0 | 1) =>
      Beta _
        (Alpha _ (Node _ (vU) A) (Leaf _ true))
        (Alpha _ (Node _ (vT) A) (Leaf _ true))
  | 2 =>
      Beta _
        (Alpha _ (Node _ (vF) A) (Leaf _ true))
        (Alpha _ (Node _ (vF) A) (Leaf _ true))
  | _ => Leaf _ true
  end.

(** Int **)

Definition Int
  (A : iLF)
  (partialV : btree iLF)
  (V : list nat)
  : btree iLF
  :=
  match A with
  | iAtom B => Leaf _ true
  | iNeg B =>
      unary_op A B partialV (vF) Int_neg_def
  | iDisj B C =>
      bin_op A B C partialV
        (vF)
        (vF)
        Int_disj_def_optimal
  | iConj B C =>
      bin_op A B C partialV
        (vF)
        (vF)
        Int_conj_def_optimal
  | iImpl B C =>
      bin_op A B C partialV
        (vF)
        (vF)
        Int_impl_def_optimal
  end.

(*********)

(** TESTES *)

(********)

Definition makeIt (h : iLF) :=
  (*(reverseThisList (nodeToNat*)
  (MakeWithoutPrune
     eqb_ilf
     leb_ilf
     length_ilf
     GetAllSub_iLF
     Int
     P
     h
     [0;2]
  )
        (* )) *).

Compute makeIt (P ~> P).

Fixpoint findVal (A : iLF) (v : list (node iLF)) (default : nat) :=
  match v with
  | nil => default
  | h::tl =>
      match h with
      | Node _ val B =>
          if eqb_ilf A B then val
          else findVal A tl default
      end
  end.

Fixpoint isCompatible (v1 v2 : list (node iLF)) :=
  match v1,v2 with
  | h1::tl1, h2::tl2 =>
      match h1 with
      | Node _ val1 _ =>
          if Nat.eqb val1 vT then
            match h2 with
            | Node _ val2 _ =>
                if Nat.eqb val2 vT then
                  isCompatible tl1 tl2
                else
                  false
            end
          else
            isCompatible tl1 tl2
      end
  | _, _ => true
  end.

Fixpoint restriction_aux2
  (A : iLF)
  (val : (list (list (node iLF))))
  (cval : list (node iLF)) :=
  match val with
  | nil => false
  | h::tl =>
      let vA := findVal A h 404 in
      if Nat.eqb vA vF then
        let compatible := isCompatible cval h in
        if compatible then true
        else
          restriction_aux2 A tl cval
      else
        restriction_aux2 A tl cval
  end.

Fixpoint restriction_aux1
  (val : (list (list (node iLF))))
  (cval cpcval : list (node iLF)) :=
  match cval with
  | nil => true
  | h::tl =>
      match h with
      | Node _ v A =>
          if Nat.eqb v vU then
            if (restriction_aux2 A val cpcval)
            then
              restriction_aux1 val tl cpcval
            else
              false
          else
            restriction_aux1 val tl cpcval
      end
  end.

          
Fixpoint restriction_aux (val cpval : list (list (node iLF))) :=
  match val with
  | nil => nil
  | h::tl =>
      if (restriction_aux1 cpval h h) then
        h::(restriction_aux tl cpval)
      else
        restriction_aux tl cpval
  end.
      
Fixpoint restriction_aux0 (val : list (list (node iLF))) (max : nat) :=
  match max with
  | O => val
  | S n =>
      let newVal := restriction_aux val val in
      restriction_aux0 newVal n
  end.

Definition restriction (val : list (list (node iLF))) :=
  restriction_aux0 val (List.length val).

Fixpoint makeItAll (l : list iLF) :=
  match l with
  | nil => nil
  | h::tl =>
      Pair _ _
        (reverseListOrder (Decompose eqb_ilf geb_ilf GetAllSub_iLF h))
        (reverseThisList (nodeToNat
            (restriction (makeIt h))
        ))::(makeItAll tl)
  end.

(*
Compute reverseThisList (nodeToNat ( (makeIt (P /\ Q)))).

Compute List.length (RemoveAmbiguity eqb_ilf (GetAllSub_iLF p11)).
 *)

Compute makeItAll vanDalen.
