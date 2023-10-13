(** 
    Implementation of non-deterministic matrices 
    type and methods 
 **)

(** **)

Require Import String.
Require Import List.
Require Import Nat.
Import ListNotations.

(** Pair [mixed types] **)

Inductive pair (X Y : Type) :=
| Pair : X -> Y -> pair X Y.

Definition proj_l {X Y : Type} (p : pair X Y) :=
  match p with
  | Pair _ _ a b => a
  end.

Definition proj_r {X Y : Type} (p : pair X Y) :=
  match p with
  | Pair _ _ a b => b
  end.

Definition pair_eqb {X Y : Type}
  (p1 p2 : pair X Y)
  (cmpX : X -> X -> bool)
  (cmpY : Y -> Y -> bool)
  :=
  andb (cmpX (proj_l p1) (proj_l p2))
    (cmpY (proj_r p1) (proj_r p2)).

(** Filter. **)

Fixpoint filter
  {X:Type}
  (test: X -> bool)
  (l : list X) : list X :=
  match l with
  | nil => nil
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

(* Get the nth element of a list *)
Fixpoint getNthElement
  {X : Type}
  (default : X)
  (index : nat)
  (l : list X)
  :=
  match l with
  | nil => default
  | h::tl =>
      if (eqb index 0) then h
      else getNthElement default (index-1) tl
  end.

(** Insert sort : https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html **)

Fixpoint insert
  {X : Type}
  (i : X)
  (l : list X)
  (f : X -> X -> bool) :=
  match l with
  | nil => i::nil
  | h :: t => if f i h then i :: h :: t else h :: insert i t f
  end.

Fixpoint sort
  {X : Type}
  (l : list X)
  (f : X -> X -> bool)
  : list X :=
  match l with
  | nil => nil
  | h :: t => insert h (sort t f) f
  end.

(********************)

Fixpoint getElementAt
  {X : Type}
  (d : X)
  (l : list X)
  (i : nat)
  :=
  match l with
  | nil => d
  | h::tl =>
      if (Nat.eqb i 0) then h
      else getElementAt d tl (i-1)
  end.

Definition pop
  {X : Type}
  (l : list X) default :=
  match l with nil => default | h::tl => h end.

Definition explode
  {X : Type}
  (l : list X) :=
  match l with nil => nil | h::tl => tl end.

Open Scope string_scope.

Inductive node (X : Type) :=
| Node : nat -> X -> node X.

Definition eqb_node
  {X : Type}
  (cmp : X -> X -> bool)
  (n1 n2 : node X)
  :=
  match n1, n2 with
  | Node _ nn1 nlf1, Node _ nn2 nlf2 =>
      andb (Nat.eqb nn1 nn2) (cmp nlf1 nlf2)
  end.

Inductive btree (X : Type) :=
| Leaf : bool -> btree X
| Alpha : node X -> btree X -> btree X
| Beta : btree X -> btree X -> btree X.

Fixpoint eqb_btree
  {X : Type}
  (cmp : X -> X -> bool)
  (b1 b2 : btree X)
  :=
  match b1, b2 with
  | Leaf _ _, Leaf _ _ => true
  | Alpha _ n t, Alpha _ n' t' =>
      if (eqb_node cmp n n') then
        eqb_btree cmp t t'
      else false
  | Beta _ t1 t2, Beta _ t1' t2' =>
      andb
        (eqb_btree cmp t1 t1')
        (eqb_btree cmp t2 t2')
  | _, _ => false
  end.

Fixpoint IsLFAlreadyOnList
  {X : Type}
  (cmp : X -> X -> bool)
  (L : X)
  (l : list X) :=
  match l with
  | nil => false
  | h::tl => orb (cmp L h) (IsLFAlreadyOnList cmp L tl)
  end.

Fixpoint RemoveAmbiguity
  {X : Type}
  (cmp : X -> X -> bool)
  (l : list X) :=
  match l with
  | nil => nil
  | h::tl => if (IsLFAlreadyOnList cmp h tl) then RemoveAmbiguity cmp tl
             else h::(RemoveAmbiguity cmp tl)
  end.

(*
 cmp : eqb_lf
 cmp1 : leb_lf
*)
Definition Decompose
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (split : X -> list X)
  (L : X)
  :=
  sort (RemoveAmbiguity eqb_AB (split L)) leb_AB.

Definition NumberOfAtoms
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (A : X)
  :=
  length (filter (fun a => leb (length_A a) 0)
            (Decompose eqb_AB leb_AB split A)).

Definition GetAtoms
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (A : X)
  :=
  (filter (fun a => leb (length_A a) 0) (Decompose eqb_AB leb_AB split A)).

(* numberOfComposed : number of subformulas which are not 
 atomic. *)
Definition NumberOfComposed
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (A : X)
  :=
  length (filter (fun a => negb (leb (length_A a) 0)) (Decompose eqb_AB leb_AB split A)).

Definition GetComposed
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (A : X)
  :=
  (filter (fun a => negb (leb (length_A a) 0)) (Decompose eqb_AB leb_AB split A)).

(* Compute Decompose eqb_lf leb_lf GetAllSubformulas ([](P ~> P)). *)

(* Em nossa abstração, uma valoração parcial é uma árvore. *)

(* 

Lembrando que uma nmatrix é uma tupla M = < V, D , O >
onde V é o conjunto de valores de verdade, D um subconjunto de V [valores designados], e O um mapa de interpretação.

Árvores iniciais: uma para cada combinação de V sobre o conjunto de atomos;
Exemplo

P -> Q
[ 
<P, 0>--<Q, 0>,
<P, 0>--<Q, 1>,
<P, 0>--<Q, 2>,
<P, 1>--<Q, 0>,
<P, 1>--<Q, 1>,
<P, 1>--<Q, 2>,
<P, 2>--<Q, 0>,
<P, 2>--<Q, 1>,
<P, 2>--<Q, 2>
]

Now, let the fun begin :)

*)

(* 

Função combine.

n = numero de atomos = 2
m = lista de valores de verdade = [0;1;2]

[
[0;0],
[0;1],
[0;2],
[1;0],
...,
[2;2]
]

*)

(*

W = NUMERO TOTAL DE LINHAS
X = numero de grupos
Y = numero de linha por grupo
Z = numero de atomos

 *)

(* 
   counter should always start (and restart) with 1 
*)

Fixpoint combine_aux
  (w : nat)
  (y : nat)
  (val : nat)
  (maxval : nat)
  (counter : nat)
  (lv : list nat)
  :=
  match w with
  | O => nil
  | S n =>
      if (eqb counter y) then
        if (eqb maxval val) then
          (getElementAt 0 lv val)::(combine_aux n y 0 maxval 1 lv)
        else
          (getElementAt 0 lv val)::(combine_aux n y (val+1) maxval 1 lv)
      else
        (getElementAt 0 lv val)::(combine_aux n y val maxval (counter+1) lv)
  end.

Compute getElementAt 0 [1;2;3] 2.

Compute combine_aux 9 3 0 2 1 [0;1].

Fixpoint combine
  (m : nat) (* number of atoms [to iterate] *)
  (natoms : nat) (* number of atoms *)
  (nrows : nat) (* total number of rows *)
  (lv : list nat)
  :=
  let v := List.length lv in (* number of truth values *)
  match m with
  | O => nil
  | S n =>
        (combine_aux nrows (v^(natoms-(natoms - m + 1))) 0 (v-1) 1 lv)
        ::(combine n natoms nrows lv)
  end.

Compute combine 2 2 3 [0;1].

Definition distributeVals
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (A : X) (* formula *)
  (v : list nat) (* list of truth values *)
  :=
  let natoms := NumberOfAtoms eqb_AB leb_AB length_A split A in
  let nrows := (length v)^(natoms) in
  combine natoms natoms nrows v.

Fixpoint getListNVal
  {X : Type}
  (default : X)
  (l : list (list nat))
  (index : nat)
  (atoms : list X)
  :=
  match l with
  | nil => nil
  | h::tl =>
      (Node _ (getNthElement 0 index h) (pop atoms default))
         ::(getListNVal default tl index (explode atoms))
  end.
      
Fixpoint makeInitialValuation_aux
  {X : Type}
  (default : X)
  (atomValuation : list (list nat))
  (atoms : list X)
  (nrows : nat)
  (c : nat)
  :=
  match nrows with
  | O => nil
  | S n =>
      (getListNVal default atomValuation c atoms)
        ::(makeInitialValuation_aux default atomValuation atoms n (c+1))
  end.

Definition nOfRows
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (A : X) (* formula *)
  (v : list nat) (* list of truth values *)
  :=  
  let atoms := GetAtoms eqb_AB leb_AB length_A split A in
  let natoms := length atoms in
  (length v)^(natoms).

Definition makeInitialValuation
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (default : X) 
  (A : X) (* formula *)
  (v : list nat) (* list of truth values *)
  :=
  let atoms := GetAtoms eqb_AB leb_AB length_A split A in
  let natoms := length atoms in
  let nrows := (length v)^(natoms) in
  let atomValuation := (distributeVals eqb_AB leb_AB length_A split A v) in
  makeInitialValuation_aux default atomValuation atoms nrows 0.

Fixpoint makeInitialTrees_aux
  {X : Type}
  (valuation : list (node X))
  : btree X
  :=
  match valuation with
  | nil => Leaf _ true
  | h::tl =>
      Alpha _ h (makeInitialTrees_aux tl)
  end.

Fixpoint makeInitialTrees
  {X : Type}
  (initialValuation : list (list (node X)))
  : list (btree X)
  :=
  match initialValuation with
  | nil => nil
  | h::tl => (makeInitialTrees_aux h)
               ::(makeInitialTrees tl)
  end.

(*****************)
(**** Generic make *********)
(******************)

Fixpoint make_aux
  {X : Type}
  (valT : btree X)
  (lcomp : list X)
  (eval : X -> btree X -> btree X)
  :=
  match lcomp with
  | nil => valT
  | h::tl =>
      let ntree := eval h valT in (make_aux ntree tl eval)
  end.

Fixpoint make
  {X : Type}
  (iniValT : list (btree X))
  (lcomp : list X)
  (eval : X -> btree X -> btree X)
  :=
  match iniValT with
  | nil => nil
  | h::tl => (make_aux h lcomp eval)::(make tl lcomp eval)
  end.

(********

Conversion from forest (list of trees) to matrix (list of lists) 

***********)

Fixpoint parse
  {X : Type}
  (t : btree X)
  (i : list (node X))
  : list (list (node X))
  := 
  match t with
  | Leaf _ b => if b then i::nil
                else nil
  | Alpha _ n nT =>
      parse nT (n::i)
  | Beta _ t1 t2 =>
      parse t1 i ++ parse t2 i  
  end.

Fixpoint parseVal
  {X : Type}
  (l : list (btree X)) :=
  match l with
  | nil => nil
  | h::tl => (parse h nil) :: (parseVal tl)
  end.

(* Flatten list. Turn the list of (list of (list of X)) into list of (list of X). *)

Close Scope string_scope.
Open Scope list_scope.

Fixpoint flattenList
  {X : Type}
  (l : list (list (list X)))
  :=
  match l with
  | nil => nil
  | h::tl => h++(flattenList tl)
  end.

(* Convert to nat table *)

Fixpoint nodeToNat_aux
  {X : Type}
  (l : list (node X))
  :=
  match l with
  | nil => nil
  | h::tl =>
      match h with
      | Node _ i A => i::(nodeToNat_aux tl)
      end
  end.

Fixpoint nodeToNat
  {X : Type}
  (l : list (list (node X)))
  :=
  match l with
  | nil => nil
  | h::tl => (nodeToNat_aux h)::(nodeToNat tl)
  end.

(****)

(** 

* Pruning algorithm

> This is a tree based implementation of Gratz's algorithm [ref].

 **)



(***************************)
(*
And now, algorithm (3.4)
 *)


(*

Seja A uma formula.

Seja Sub(A) o conjunto das subformulas de A

Sejam 

v0_p(A0),v0_p(A1),...,v0_p(An)
v1_p(A0),v1_p(A1),...,v1_p(An)
.
.
.
vn_p(A0),vn_p(A1),...,vn_p(An)

Valoraçoes parciais [linhas da matriz de valoraçoes de A].

====

Tome uma linha vx_p e uma fórmula Ax de Sub(A).

----

V1 (original)

Remover vx_p onde vx_p(Ax) = 1 da matriz sse

Não existe linha vy_p tal que

1) vy_p(Ax) = 0; e
2) Para todo An em Sub(A), vx_p(An) = 2 -> vy_p(An) = 2

---------------

V2 (negaçao) 

NAO Remover vx_p onde vx_p(Ax) = 1 da matriz sse

Existe linha vy_p tal que

1) vy_p(Ax) = 0; e
2) Para todo An em Sub(A), vx_p(An) = 2 -> vy_p(An) = 2

 *)

Fixpoint getValuation_aux
  {X : Type}
  (default : nat)
  (A : X)
  (vp : list (node X))
  (cmp : X -> X -> bool)
  :=
  match vp with
  | nil => default
  | h::tl =>
      match h with
      | Node _ i B =>
          if (cmp A B) then i
          else getValuation_aux default A tl cmp
      end
  end.

Fixpoint getValuation
  {X : Type}
  (default : nat)
  (A : X)
  (matrix : list (list (node X)))
  (cmp : X -> X -> bool)
  :=
  match matrix with
  | nil => nil
  | h::tl =>
      (getValuation_aux default A h cmp)
        ::(getValuation default A tl cmp)
  end.

Fixpoint reverseListOrder
  {X : Type}
  (l : list X)
  :=
  match l with
  | nil => nil
  | h::tl => (reverseListOrder tl)++(h::nil)
  end.

Compute reverseListOrder [0;1;2;3].

(* 

l1(B) = 2 -> l2 (B) = 2 

l1 := [0;2;2;1;2]
l2 := [2;2;2;1;2]
: true

l1 := [0;2;2;1;2]
l2 := [2;0;2;1;2]
: false

 *)

Fixpoint compare_aux
  {X : Type}
  (pruning : nat -> bool)
  (cmp : X -> X -> bool)
  (A : X)
  (l : list (node X))
  :=
  match l with
  | nil => true
  | h::tl =>
      match h with
      | Node _ i B =>
          if (cmp A B)
          then
            if (pruning i)
            then compare_aux pruning cmp A tl
            else false
          else
            compare_aux pruning cmp A tl
      end
  end.

Fixpoint compare
  {X : Type}
  (pruning : list (nat -> bool))
  (cmp : X -> X -> bool)
  (l1 l2 : list (node X))
  :=
  match l1 with
  | nil => true
  | h::tl =>
      match h with
      | Node _ i A =>
          if (getElementAt (fun n => false) pruning 0) i then
            if (compare_aux
                  (getElementAt (fun n => true) pruning 1)
                  cmp A l2)
            then
              compare pruning cmp tl l2
            else
              false
          else
            compare pruning cmp tl l2
      end
  end.

(* Compute compare

  ((fun a => Nat.eqb a 2)
     ::((fun a => Nat.eqb a 2))::nil)
          
  eqb_lf

  [
    (Node LF 0 (! "P"));
    (Node LF 1 ([](! "P")));
    (Node LF 1 ([]([](! "P"))));
    (Node LF 1 ([]([](! "P" ~> ! "P"))))
  ]

  [
    (Node LF 1 (! "P"));
    (Node LF 2 ([]([](! "P"))));
    (Node LF 0 ([](! "P")));
    (Node LF 0 ([]([](! "P" ~> ! "P"))))
  ]
.*)


Fixpoint EvalForest_aux5
  {X : Type}
  (cmp : X -> X -> bool)
  (b : btree X)
  (A : X)
  (p : bool) (* true iff pruning candidate *)
  :=
  match b with
  | Leaf _ t => Leaf _ (andb t p)
  | Alpha _ n t =>
      match n with
      | Node _ i L =>
          if (andb
                (cmp A L)
                (Nat.eqb i 0))
          then
            Alpha _ n (EvalForest_aux5 cmp t A true)
          else
            Alpha _ n (EvalForest_aux5 cmp t A p)
      end
  | Beta _ t1 t2 =>
      Beta _
        (EvalForest_aux5 cmp t1 A p)
        (EvalForest_aux5 cmp t2 A p)
  end.
      
Fixpoint EvalForest_aux4
  {X : Type}
  (cmp : X -> X -> bool)
  (b : btree X)
  (ln : list X)
  :=
  match ln with
  | nil => nil
  | h::tl =>
      (Pair _ _ h (parse (EvalForest_aux5 cmp b h false) nil))
        ::(EvalForest_aux4 cmp b tl)
  end.

(* Definition b1 :=
  Alpha LF (Node LF 0 (! "P"))
         (Beta LF (Alpha LF (Node LF 1 (! "P" ~> ! "P")) (Alpha LF (Node LF 0 ([] (! "P" ~> ! "P"))) (Leaf LF true)))
            (Alpha LF (Node LF 2 (! "P" ~> ! "P")) (Alpha LF (Node LF 2 ([] (! "P" ~> ! "P"))) (Leaf LF true)))).

Definition b1' :=
  Alpha LF (Node LF 0 (! "P"))
         (Beta LF (Alpha LF (Node LF 1 (! "P" ~> ! "P")) (Alpha LF (Node LF 0 ([] (! "P" ~> ! "P"))) (Leaf LF true)))
            (Alpha LF (Node LF 1 (! "P" ~> ! "P")) (Alpha LF (Node LF 2 ([] (! "P" ~> ! "P"))) (Leaf LF true)))).

Definition b2 :=
  Alpha LF (Node LF 0 (! "P"))
    (Alpha LF (Node LF 1 (! "P" ~> ! "P"))
       (Alpha LF (Node LF 0 ([] ! "P"))
          (Leaf LF true))).

Definition b3 :=
  Alpha LF (Node LF 1 (! "P"))
         (Alpha LF (Node LF 0 (! "Q"))
            (Alpha LF (Node LF 0 (! "P" ~> ! "Q")) (Alpha LF (Node LF 0 ([] (! "P" ~> ! "Q"))) (Leaf LF false)))).

Definition ln1 :=
  [([](! "P" ~> ! "P")); ((! "P" ~> ! "Q"))].

Definition ln2 :=
  [(! "P");(! "P" ~> ! "P")].

Definition ln3 :=
  [(! "P" ~> ! "Q");(! "P");(! "Q")].

Compute eqb_btree eqb_lf b1 b1'. *)

Fixpoint lookForEmpty
  {X : Type}
  (ln : list (list (list (node X))))
  :=
  match ln with
  | nil => false
  | h::tl =>
      match h with
      | nil => true
      | _ => lookForEmpty tl
      end
  end.

Fixpoint EvalForest_aux7
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (l1 : list (node X))
  (l2 : list (list (node X)))
  :=
  match l2 with
  | nil => false
  | h::tl =>
      let eval := compare pruning cmp l1 h in
      if eval then true
      else EvalForest_aux7 cmp pruning l1 tl
  end.

Fixpoint EvalForest_aux6
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (l1 : list (node X))
  (ln : list (pair X (list (list (node X)))))
  :=
  match ln with
  | nil => nil
  | h::tl =>
      (Pair _ _ (proj_l h) (EvalForest_aux7 cmp pruning l1 (proj_r h)))
        ::(EvalForest_aux6 cmp pruning l1 tl)
  end.

Fixpoint completeValuation_aux
  {X : Type}
  (cmp : X -> X -> bool)
  (l : list (pair X bool))
  (A : X)
  :=
  match l with
  | nil => false
  | h::tl =>
      if (cmp (proj_l h) A) then
        if (proj_r h) then true
        else completeValuation_aux cmp tl A
      else completeValuation_aux cmp tl A
  end.
                             
Fixpoint completeValuation
  {X : Type}
  (cmp : X -> X -> bool)
  (lf : list X)
  (l : list (pair X bool))
  :=
  match lf with
  | nil => true
  | h::tl =>
      andb
        (completeValuation_aux cmp l h)
        (completeValuation cmp tl l)
  end.

Fixpoint EvalForest_aux3
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (m : list (btree X)) (* list of all trees *)
  (ln : list (node X)) (* will compare ln with every eval_aux4 *)
  (lf : list X)
  (eval : list (pair X bool))
  :=
  match m with
  | nil => completeValuation cmp lf eval
  | h::tl =>
      let compareTo := (EvalForest_aux4 cmp h lf) in
      let localEval := EvalForest_aux6 cmp pruning ln compareTo in
      EvalForest_aux3 cmp pruning tl ln lf (localEval ++ eval)
  end.

(** Essa função retorna a árvore com as marcas de poda **)
Fixpoint EvalForest_aux2
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (m : list (btree X)) (* list of all trees *)
  (b : btree X) (* current tree *)
  (ln : list (node X)) (* local branch *)
  (lf : list X) (* list of formulas A with v(A) = 1 in the local branch *)
  :=
  match b with
  | Leaf _ _ =>
      if (Nat.eqb (List.length lf) 0) then
        Leaf _ true
      else
        let eval := EvalForest_aux3 cmp pruning m ln lf nil in
        Leaf _ eval
  | Alpha _ n t =>
      match n with
      | Node _ i L =>
          if (getElementAt (fun n => true) pruning 2) i then
            Alpha _ n (EvalForest_aux2 cmp pruning m t (n::ln) (L::lf))
          else
            Alpha _ n (EvalForest_aux2 cmp pruning m t (n::ln) lf)
      end
  | Beta _ t1 t2 =>
      Beta _
        (EvalForest_aux2 cmp pruning m t1 ln lf)
        (EvalForest_aux2 cmp pruning m t2 ln lf)
  end.

Fixpoint EvalForest_aux
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (m m_copy : list (btree X))
  :=
  match m with
  | nil => nil
  | h::tl =>
      (EvalForest_aux2 cmp pruning m_copy h nil nil)
        ::(EvalForest_aux cmp pruning tl m_copy)
  end.

(* Gratz's filter with trees *)
Definition EvalForest
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (m : list (btree X))
  :=
  match m with
  | _ => EvalForest_aux cmp pruning m m
  end.

(**************)


Definition MakeWithoutPrune
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (logic : X -> btree X -> btree X)
  (default: X)
  (A : X)
  (V : list nat)
  :=
  let init :=
    makeInitialTrees
      (makeInitialValuation
         eqb_AB
         leb_AB
         length_A
         split
         default
         A
         V)
  in
  let sub_A := GetComposed eqb_AB leb_AB length_A split A in
  let forest := make init sub_A logic in
  flattenList (parseVal (forest)).

(* 

HEURÍSTICAS
------------

Uma heurística de um algoritmo é admissível quando leva a um resultado (output) equivalente ao resultado obtido pelo mesmo algoritmo sem heurística.

Heurística trivial: parar quando o algoritmo não produzir nenhuma alteração na árvore. Essa heurística é trivialmente admissível e aparece no artigo de Gratz.

Novas heurísticas: ?

(não-admissibilidade poderia ser aceitável?)

 *)

(* true iff lb1 = lb2 *)
Fixpoint forest_cmp
  {X : Type}
  (cmp : X -> X -> bool)
  (lb1 lb2 : list (btree X))
  :=
  match lb1, lb2 with
  | nil, nil => true
  | h::tl, h'::tl' =>
      if eqb_btree cmp h h' then
        forest_cmp cmp tl tl'
      else
        false
  | _,_ => false
  end.

(* max is the maximum number of removals on the matrix 
   which corresponds to the number of rows
*)
Fixpoint MakeWithPrune_aux
  {X : Type}
  (cmp : X -> X -> bool)
  (pruning : list (nat -> bool))
  (m : list (btree X))
  (max : nat)
  :=
  match max with
  | O => EvalForest cmp pruning m
  | S n =>
      let nmatrix := EvalForest cmp pruning m in
      if (negb (forest_cmp cmp m nmatrix)) then (* heuristic *)
        nmatrix (* you can stop here *)
      else MakeWithPrune_aux cmp pruning nmatrix n
  end.

Definition MakeWithPrune
  {X : Type}
  (eqb_AB leb_AB : X -> X -> bool)
  (length_A : X -> nat)
  (split : X -> list X)
  (logic : X -> btree X -> btree X)
  (pruning : list (nat -> bool))
  (default: X)
  (A : X)
  (V : list nat)
  :=
  let init :=
    makeInitialTrees
      (makeInitialValuation
         eqb_AB
         leb_AB
         length_A
         split
         default
         A
         V)
  in
  let rows_A := nOfRows eqb_AB leb_AB length_A split A V in
  let sub_A := GetComposed eqb_AB leb_AB length_A split A in
  let forest := make init sub_A logic in
  flattenList (parseVal (MakeWithPrune_aux eqb_AB pruning forest rows_A)).

