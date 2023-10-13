(*

Intuitionistic propositional logic using the RNmatrix described in:

TRACTABLE DEPTH-BOUNDED APPROXIMATIONS TO SOME PROPOSITIONAL LOGICS. TOWARDS MORE REALISTIC MODELS OF LOGICAL AGENTS / A.j. Solares Rojas ; supervisore: A. Zamansky, M. D'Agostino ; coordinatore: A. Pinotti. Dipartimento di Filosofia Piero Martinetti, 2022 Jul 15. 34. ciclo, Anno Accademico 2021.

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

(*

Convention: 

0 represents 0
1 represents 1
2 represents u

 *)

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

(* Negation *)

Definition Int_neg_def
  (* ~ [vA] *)
  (A : iLF)
  (vB : nat)
  : btree iLF
  :=
  match vB with
  | 0 =>
      (Alpha _ (Node _ 1 A) (Leaf _ true))
  | 1 =>
      (Alpha _ (Node _ 0 A) (Leaf _ true))
  | _ =>
      Beta _
        (Alpha _ (Node _ 0 A) (Leaf _ true))
        (Alpha _ (Node _ 2 A) (Leaf _ true))
  end.

(* Conjunction *)

Definition Int_conj_def
  (* [vA] /\ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | 0 =>
      Alpha _ (Node _ 0 A) (Leaf _ true)
  | 1 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      end
  | _ =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ 0 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      end
  end.

(* Disjunction *)

Definition Int_disj_def
  (* [vA] \/ [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | 0 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      end
  | 1 =>
      Alpha _ (Node _ 1 A) (Leaf _ true)
  | _ =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      end
  end.

(* Implication *)

Definition Int_impl_def
  (* [vA] -> [vB] *)
  (A : iLF)
  (vB vC : nat)
  : btree iLF
  :=
  match vB with
  | 0 =>
      Alpha _ (Node _ 1 A) (Leaf _ true)
  | 1 =>
      match vC with
      | 0 =>
          Alpha _ (Node _ 0 A) (Leaf _ true)
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Alpha _ (Node _ 2 A) (Leaf _ true)
      end
  | _ =>
      match vC with
      | 0 =>
          Beta _
            (Alpha _ (Node _ 0 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      | 1 =>
          Alpha _ (Node _ 1 A) (Leaf _ true)
      | _ =>
          Beta _
            (Alpha _ (Node _ 1 A) (Leaf _ true))
            (Alpha _ (Node _ 2 A) (Leaf _ true))
      end
  end.

(** The logic. **)

Definition Int3Ni
  (A : iLF)
  (partialV : btree iLF)
  (V : list nat)
  : btree iLF
  :=
  match A with
  | iAtom B => Leaf _ true
  | iNeg B =>
      unary_op A B partialV 0 Int_neg_def
  | iDisj B C =>
      bin_op A B C partialV
        0
        0
        Int_disj_def
  | iConj B C =>
      bin_op A B C partialV
        0
        0
        Int_conj_def
  | iImpl B C =>
      bin_op A B C partialV
        0
        0
        Int_impl_def
  end.

Definition makeIt (h : iLF) :=
            (MakeWithoutPrune
               eqb_ilf
               leb_ilf
               length_ilf
               GetAllSub_iLF
               Int3Ni
               P
               h
               [0;1;2]
            ).

(* 3-refinement (Def. 5.7.3) *)
Fixpoint is3Refinement (v1 v2 : list (node iLF)) :=
  match v1,v2 with
  | h1::tl1, h2::tl2 =>
      match h1 with
      | Node _ val1 _ =>
          if (Nat.eqb val1 2) then
            is3Refinement tl1 tl2
          else
            match h2 with
            | Node _ val2 _ =>
                if Nat.eqb val1 val2 then
                  is3Refinement tl1 tl2
                else
                  false
            end
      end
  | _, _ => true
  end.

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

Definition detRestriction_aux (t : btree iLF) (default : nat) :=
  match t with
  | Alpha _ n _ =>
      match n with
      | Node _ val _ => val
      end
  | _ => default
  end.

(* Deterministic restriction (Def. 5.7.4) *)
(* 404 --- undefined *)
Definition detRestriction (A : iLF) (v : list (node iLF)) :=
  match A with
  | ! _ => findVal A v 404
  | ~ B =>
      let vB := findVal B v 404 in 
      let valTree := Int_neg_def A vB in
      detRestriction_aux valTree 404 
  | B /\ C =>
      let vB := findVal B v 404 in
      let vC := findVal C v 404 in 
      let valTree := Int_conj_def A vB vC in
      detRestriction_aux valTree 404
  | B \/ C =>
      let vB := findVal B v 404 in
      let vC := findVal C v 404 in 
      let valTree := Int_disj_def A vB vC in
      detRestriction_aux valTree 404
  | B ~> C =>
      let vB := findVal B v 404 in
      let vC := findVal C v 404 in 
      let valTree := Int_impl_def A vB vC in
      detRestriction_aux valTree 404
  end.

(* This function check for Def. 5.7.5 clausule i *)
Fixpoint restriction_aux2
  (A : iLF)
  (val : (list (list (node iLF))))
  (cval : list (node iLF)) :=
  match val with
  | nil => false
  | h::tl =>
      (* Check if cval <= h *)
      if is3Refinement cval h then
        let detRest := detRestriction A h in
        if (Nat.eqb detRest 1) then
          true
        else
          restriction_aux2 A tl cval
      else
        restriction_aux2 A tl cval
  end.

(* This function check for Def. 5.7.5 clausule ii *)
Fixpoint restriction_aux3
  (A : iLF)
  (val : (list (list (node iLF))))
  (cval : list (node iLF)) :=
  match val with
  | nil => false
  | h::tl =>
      (* Check if cval <= h *)
      if is3Refinement cval h then
        let detRest := detRestriction A h in
        if andb
             (negb (Nat.eqb detRest 404))
             (negb (Nat.eqb detRest 1))
        then
          true
        else
          restriction_aux3 A tl cval
      else
        restriction_aux3 A tl cval
  end.

Fixpoint restriction_aux1
  (val : (list (list (node iLF))))
  (cval cpcval : list (node iLF)) :=
  match cval with
  | nil => true
  | h::tl =>
      match h with
      | Node _ v A =>
          if Nat.eqb v 2 then
            if andb
                 (restriction_aux2 A val cpcval) (* 5.7.5 (i) *)
                 (restriction_aux3 A val cpcval) (* 5.7.5 (ii) *)
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

Compute makeItAll vanDalen.
