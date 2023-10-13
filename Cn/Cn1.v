(*

Implementation of Cn using the RNmatrix described in:

CONIGLIO, Marcelo E.; TOLEDO, Guilherme V. Two Decision Procedures for da Costa’s C n Logics Based on Restricted Nmatrix Semantics. Studia Logica, v. 110, n. 3, p. 601-642, 2022.

Note that, in this implementation, the convention is:

Let n > 2 be a natural number. For each C(n-2), we attach a list V = [0,...,n-1,n], where

0 = True
.
.
.
n-1 = inconsistent value
n = False

*)

Add LoadPath "../" as Main.
Require Import Nat.
Require Import Main.Forest.

Notation "( x , y )" := (Pair _ _ x y).

Definition Atom : Type := nat.

Inductive cnLF :=
| cnAtom : Atom -> cnLF
| cnNeg : cnLF -> cnLF
| cnConj : cnLF -> cnLF -> cnLF
| cnDisj : cnLF -> cnLF -> cnLF
| cnImpl : cnLF -> cnLF -> cnLF.

Notation "! A" := (cnAtom A) (at level 10).
Notation "~ A" := (cnNeg A).
Notation "A ~> B" := (cnImpl A B) (at level 90).
Notation "A \/ B" := (cnDisj A B).
Notation "A /\ B" := (cnConj A B).

Definition P := ! 0.
Definition Q := ! 1.

Check P /\ ~P : cnLF.
Check (P /\ ~P) ~> Q : cnLF.

Fixpoint eqb_cnlf (A : cnLF) (B : cnLF) :=
  match A with
  | ! P => match B with
              | cnAtom Q => if (Nat.eqb P Q) then true
                          else false
              | _ => false
              end
  | ~ P => match B with
           | ~ Q => eqb_cnlf P Q
           | _ => false
           end
  | P ~> Q => match B with
              | R ~> T => andb (eqb_cnlf P R) (eqb_cnlf Q T)
              | _ => false
              end
  | P /\ Q => match B with
              | R /\ T => andb (eqb_cnlf P R) (eqb_cnlf Q T)
              | _ => false
              end
  | P \/ Q => match B with
              | R \/ T => andb (eqb_cnlf P R) (eqb_cnlf Q T)
              | _ => false
              end
  end.

Fixpoint length_cnlf (A : cnLF) :=
  match A with
  | ! P => 0
  | ~ P => 1 + length_cnlf P
  | P ~> Q => 1 + length_cnlf P + length_cnlf Q
  | P /\ Q => 1 + length_cnlf P + length_cnlf Q
  | P \/ Q => 1 + length_cnlf P + length_cnlf Q
  end.

Definition leb_cnlf (A : cnLF) (B : cnLF) :=
  leb (length_cnlf A) (length_cnlf B).

Definition geb_cnlf (A : cnLF) (B : cnLF) :=
  negb (Nat.leb (length_cnlf A) (length_cnlf B)).

Fixpoint GetAllSub_cnLF (L : cnLF) :=
  match L with
  | ! A => (! A)::nil
  | ~ A => (~ A)::(GetAllSub_cnLF A)
  | A ~> B => (A ~> B)::((GetAllSub_cnLF A)++(GetAllSub_cnLF B))
  | A /\ B => (A /\ B)::((GetAllSub_cnLF A)++(GetAllSub_cnLF B))
  | A \/ B => (A \/ B)::((GetAllSub_cnLF A)++(GetAllSub_cnLF B))
  end.


(* da Costa's C_n generator *)

(* A^n *)
Fixpoint cngen (A : cnLF) (n : nat) : cnLF :=
  match n with
  | O => A
  | S m => ~ ((cngen A m) /\ (~ (cngen A m)))
  end.

(* A^(n) *)
Fixpoint cngen2 (A : cnLF) (n : nat) : cnLF :=
  match n with
  | O => A
  | S O => cngen A 1
  | S m => (cngen2 A m) /\ (cngen A (S m))
  end.


Definition A := cnAtom 0.

Example ex0 :
    cngen A 0 = ! 0.
Proof. reflexivity. Qed.

Example ex1 :
  cngen A 1 = ~ (! 0 /\ ~ ! 0).
Proof. reflexivity. Qed.

Example ex2 :
  cngen A 2 = ~ (~ (! 0 /\ ~ ! 0) /\ ~ ~ (! 0 /\ ~ ! 0)).
Proof. reflexivity. Qed.

(* Tree generator *)

(* First, we have to generate the truth values. 
They are tuples, wich means that the order is important. 
They are, therefore, somewhat like lists. *)

Require Import List.
Import ListNotations.

Fixpoint genT (n : nat) : list nat :=
  match n with
  | O => nil
  | S n => n::(genT n)
  end.

Fixpoint genBn_aux2 (n : nat) :=
  match n with
  | O => nil
  | S m =>
      true::(genBn_aux2 m)
  end.

Fixpoint genBn_aux3 (n : nat) (l : list bool) :=
  match l with
  | nil => nil
  | h::tl =>
      if (Nat.eqb n 0) then
        false::tl
      else
        true::(genBn_aux3 (n-1) tl)
  end.

Definition l1 := genBn_aux2 5.

(* 

genBn_aux3 n L

1 < n >= |L|

Valores de inconsistencia.

n = 0 = F
n = 1 = T

 *)

Fixpoint genBn_aux1 (n max maxi : nat) (base : list bool) :=
  match maxi with
  | O => nil
  | S m =>
      if (Nat.eqb n max) then (genBn_aux3 n base)::nil
      else
        let tm := genBn_aux3 n base in
        tm::(genBn_aux1 (n+1) max m base)
  end.

Definition Bn (m : nat) :=
  let n := m + 1 in
  let base := genBn_aux2 n in
  let T := genBn_aux3 1 base in
  let F := genBn_aux3 0 base in
  if (Nat.leb n 1) then T::F::nil
  else
    let I := genBn_aux1 2 n n base in
    T::I++(F::nil).

Fixpoint Dn_aux
  (bn : list  (list bool))
  : list (list bool)
  :=
  match bn with
  | nil => nil
  | h::tl => 
      if Nat.eqb (List.length tl) 0 then
        nil
      else
        h::(Dn_aux tl)
  end.

(*

Dn -- designated values
In -- inconsistent values
Tn -- boolean truth
Fn -- boolean falsity

*)

Definition Dn
  (bn : list  (list bool))
  : list (list bool)
  :=
  Dn_aux bn.

Definition In
  (bn : list  (list bool))
  : list (list bool)
  :=
  explode (Dn bn).

Definition Tn
  (bn : list  (list bool))
  : list (list bool)
  :=
  [pop bn nil].

Definition Fn
  (bn : list  (list bool))
  : list (list bool)
  :=
  [getElementAt nil bn ((length bn)-1)].

Definition bn1 := Bn 5.

(********)

Fixpoint pairwise_aux
  (n : nat)
  (bn : list (list bool)) :=
  match bn with
  | nil => nil
  | h::tl =>
      (Pair _ _ n h)::(pairwise_aux (n+1) tl)
  end.

(*

Let F be a function that goes from a natural number to  a truth value (tuple). 

pairwise is a map that allow us to go from nat Forest to Cn valuation

*)

Definition pairwise
  (bn : list (list bool)) :=
  pairwise_aux 0 bn.

(* Auxiliary functions *)

Definition getAlpha (A : cnLF) :=
  match A with
  | ~ B =>
      match B with
      | C /\ D => C
      | _ => A
      end
  | _ => A
  end.

Definition filterCn
  (A : cnLF)
  :=
  match A with
  | B /\ C =>
      match C with
      | ~ D => eqb_cnlf D B
      | _ => false
      end
  | _ => false
  end.

Definition filterCn_inv
  (A : cnLF)
  :=
  match A with
  | B /\ C =>
      match B with
      | ~ D => eqb_cnlf D C
      | _ => false
      end
  | _ => false
  end.

Definition filterCn2
  (A : cnLF)
  :=
  match A with
  | ~ B => orb (filterCn B) (filterCn_inv B)
  | _ => false
  end.

Definition filterCn3
  (A : cnLF)
  :=
  match A with
  | ~ B =>
      andb (filterCn2 A) (negb (filterCn2 (getAlpha A)))
  | _ => false
  end.

Fixpoint unary_op
  (A B : cnLF)
  (partialV : btree cnLF)
  (vB : nat)
  (op : cnLF -> nat -> list nat -> nat -> btree cnLF)
  (V : list nat)
  (alpha_V : nat)
  : btree cnLF
  :=
  let alpha := getAlpha A in
  match partialV with
  | Leaf _ t =>
      if t then
        op A vB V alpha_V
      else
        Leaf _ t
  | Alpha _ n t =>
      match n with
      | Node _ i D =>
          if (eqb_cnlf alpha D) then
            Alpha _ n (unary_op A B t vB op V i)
          else
            if (eqb_cnlf B D) then
              Alpha _ n (unary_op A B t i op V alpha_V)
            else Alpha _ n (unary_op A B t vB op V alpha_V)
      end
  | Beta _ t1 t2 =>
      Beta _
        (unary_op A B t1 vB op V alpha_V)
        (unary_op A B t2 vB op V alpha_V)
  end.

Fixpoint bin_op
  (A B C : cnLF)
  (partialV : btree cnLF)
  (vB vC : nat)
  (op : cnLF -> nat -> nat -> list nat -> btree cnLF)
  (V : list nat)
  : btree cnLF
  :=
  match partialV with
  | Leaf _ t =>
      if t then
        op A vB vC V
      else
        Leaf _ t
  | Alpha _ n t =>
      match n with
      | Node _ i D =>
          if (eqb_cnlf B D) then
            if (eqb_cnlf C D) then
              Alpha _ n (bin_op A B C t i i op V)
            else
              Alpha _ n (bin_op A B C t i vC op V)
          else
            if (eqb_cnlf C D) then
              Alpha _ n (bin_op A B C t vB i op V)
            else Alpha _ n (bin_op A B C t vB vC op V)
      end
  | Beta _ t1 t2 =>
      Beta _
        (bin_op A B C t1 vB vC op V)
        (bin_op A B C t2 vB vC op V)
  end.

Fixpoint listToTree
  (dn : list nat)
  (A : cnLF)
  : btree cnLF
  :=
  match dn with
  | nil => Leaf _ true
  | h::tl =>
      if (Nat.eqb (List.length tl) 0) then
          (Alpha _ (Node _ h A) (Leaf _ true))
      else
        Beta _
          (Alpha _ (Node _ h A) (Leaf _ true))
          (listToTree tl A)
  end.
             
(* 

In what follows, we assume 

vB = 0 --- T 
vB = (lenghtV-1) --- F

 *)

Fixpoint removeLast_aux
  {X : Type}
  (l : list X)
  : list X
  :=
  match l with
  | nil => nil
  | h::tl => 
      if Nat.eqb (List.length tl) 0 then
        nil
      else
        h::(removeLast_aux tl)
  end.

Definition removeLast
  {X : Type}
  (l : list X)
  : list X
  :=
  removeLast_aux l.

Definition Cn_neg_def
  (* [vA] = ~ [vB] *)
  (A : cnLF)
  (vB : nat)
  (V : list nat)
  (alpha_V : nat) (* Here, alpha_V = k. *)
  : btree cnLF
  :=
  let T := 0 in
  let F := ((List.length V) - 1) in
  let Dn := (removeLast V) in
  if
    (andb
       (negb (Nat.leb alpha_V 1))
       (andb
          (filterCn3 A) (* Check if A is B^1 for some B *)
          (andb (* Check if v(A) = k , 1 <= k < n. *)
             (negb (Nat.eqb alpha_V T))
             (negb (Nat.eqb alpha_V F))))) then
    listToTree [alpha_V-1] A
  else
    if (Nat.eqb vB 0) then (* vB is T *)
      Alpha _ (Node _ F A) (Leaf _ true)
    else
      if (Nat.eqb vB ((List.length V) - 1)) then
        (* vB is F *)
        Alpha _ (Node _ T A) (Leaf _ true)
      else (* vB is In *) 
        listToTree Dn A.

Definition Cn_conj_def
  (* [vA] = [vB] /\ [vC] *)
  (A : cnLF)
  (vB vC : nat) (* Here, k = vB OR k = vC *)
  (V : list nat)
  : btree cnLF
  :=
  let T := 0 in
  let F := ((List.length V) - 1) in
  let Dn := (removeLast V) in
  let In := explode Dn in
  if
    (* Check if A = B /\ ~B OR A = ~B /\ B *)
    (orb (andb (filterCn A)
            (andb
               (negb (Nat.eqb vB T))
               (negb (Nat.eqb vB F))))
            (andb (filterCn_inv A)
               (andb
                  (negb (Nat.eqb vC T))
                  (negb (Nat.eqb vC F))))) then
    if (filterCn A) then
      (* If A = B /\ ~B, then k = vB *)
      if (Nat.eqb vB 1) then
        listToTree [T] A
      else
        listToTree In A
    else
      (* If A = ~B /\ B, then k = vC *)
      if (Nat.eqb vC 1) then
        listToTree [T] A
      else
        listToTree In A
  else
    if orb (Nat.eqb vB F) (Nat.eqb vC F) then 
      (* vB or vC is F *)
      Alpha _ (Node _ F A) (Leaf _ true)
    else
      if andb (Nat.eqb vB T) (Nat.eqb vC T) then
        (* vB and vC is T *)
        Alpha _ (Node _ T A) (Leaf _ true)
      else
        listToTree Dn A.

Definition Cn_impl_def
  (* [vA] = [vB] ~> [vC] *)
  (A : cnLF)
  (vB vC : nat)
  (V : list nat)
  : btree cnLF
  :=
  let T := 0 in
  let F := ((List.length V) - 1) in
  if Nat.eqb vB T then (* vB is T *)
    if Nat.eqb vC T then (* vC is T *)
      Alpha _ (Node _ T A) (Leaf _ true)
    else if Nat.eqb vC F then (* vC is F *)
           Alpha _ (Node _ F A) (Leaf _ true)
         else (* vC is In *)
           listToTree (removeLast V) A
  else
    if Nat.eqb vB F then
      if Nat.eqb vC T then
        Alpha _ (Node _ T A) (Leaf _ true)
      else if Nat.eqb vC F then
             Alpha _ (Node _ T A) (Leaf _ true)
           else
             listToTree (removeLast V) A
    else
      if Nat.eqb vC F then
        Alpha _ (Node _ F A) (Leaf _ true)
      else
        listToTree (removeLast V) A.

Definition Cn_disj_def
  (* [vA] = [vB] /\ [vC] *)
  (A : cnLF)
  (vB vC : nat)
  (V : list nat)
  : btree cnLF
  :=
  let T := 0 in
  let F := ((List.length V) - 1) in
  if (Nat.eqb vB T) then
    if (Nat.eqb vC T) then
      Alpha _ (Node _ T A) (Leaf _ true)
    else
      if (Nat.eqb vC F) then
        Alpha _ (Node _ T A) (Leaf _ true)
      else
        listToTree (removeLast V) A
  else
    if (Nat.eqb vB F) then
      if (Nat.eqb vC T) then
        Alpha _ (Node _ T A) (Leaf _ true)
      else
        if (Nat.eqb vC F) then
          Alpha _ (Node _ F A) (Leaf _ true)
        else
          listToTree (removeLast V) A 
    else
      (* vB é In *)
      listToTree (removeLast V) A.

Definition Cn
  (A : cnLF)
  (partialV : btree cnLF)
  (V : list nat)
  : btree cnLF
  :=
  match A with
  | ! B => Leaf _ true
  | ~ B =>
      unary_op A B partialV 0 Cn_neg_def V 0
  | B ~> C =>
      bin_op A B C partialV 0 0 Cn_impl_def V
  | B \/ C =>
      bin_op A B C partialV 0 0 Cn_disj_def V
  | B /\ C =>
      bin_op A B C partialV 0 0 Cn_conj_def V
  end.


(*************)

Definition propag_consist_conj_1 :=
  ((cngen2 P 1) /\ (cngen2 Q 1)) ~> (cngen2 (P /\ Q) 1).
Definition propag_consist_disj_1 :=
  ((cngen2 P 1) /\ (cngen2 Q 1)) ~> (cngen2 (P \/ Q) 1).
Definition propag_consist_impl_1 :=
  ((cngen2 P 1) /\ (cngen2 Q 1)) ~> (cngen2 (P ~> Q) 1).

Definition propag_consist_conj_2 :=
  ((cngen2 P 2) /\ (cngen2 Q 2)) ~> (cngen2 (P /\ Q) 2).
Definition propag_consist_disj_2 :=
  ((cngen2 P 2) /\ (cngen2 Q 2)) ~> (cngen2 (P \/ Q) 2).
Definition propag_consist_impl_2 :=
  ((cngen2 P 2) /\ (cngen2 Q 2)) ~> (cngen2 (P ~> Q) 2).

Definition propag_consist_conj_3 :=
  ((cngen2 P 3) /\ (cngen2 Q 3)) ~> (cngen2 (P /\ Q) 3).

Definition propag_consist_conj_4 :=
  ((cngen2 P 4) /\ (cngen2 Q 4)) ~> (cngen2 (P /\ Q) 4).

Definition makeIt (h : cnLF) :=
  (MakeWithoutPrune
    eqb_cnlf
    leb_cnlf
    length_cnlf
    GetAllSub_cnLF
    Cn
    P
    h
    [0;1;2]).

Fixpoint makeItAll (l : list cnLF) :=
  match l with
  | nil => nil
  | h::tl =>
      Pair _ _
        (reverseListOrder (Decompose eqb_cnlf geb_cnlf GetAllSub_cnLF h))
        (reverseThisList (nodeToNat
            (makeIt h)
        ))::(makeItAll tl)
  end.


Compute makeItAll [propag_consist_conj_1].
