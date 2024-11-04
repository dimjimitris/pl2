Require Import Coq.Strings.String Coq.Init.Nat Lia.

Ltac inv H :=
  inversion H; subst; clear H.

Definition state (A : Type) := string -> A.

Definition empty_st {A : Type} (def : A) : state A := fun _ => def.

Definition update_st {A : Type} (st : state A) (x : string) (v : A) : state A :=
  fun z => if (x =? z)%string then v else st z.

Notation "'_' '!->' 0" := (empty_st 0)
  (at level 100, right associativity).
Notation "x '!->' v ';' m" := (update_st m x v)
                              (at level 100, v at next level, right associativity).

(** Arithmetic expressions: *)

Inductive aexp : Type :=
| ANum : nat -> aexp
| AId : string -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| ADiv : aexp -> aexp -> aexp
| AMod : aexp -> aexp -> aexp.


(** Boolean expressions: *)

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BLt : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr :  bexp -> bexp -> bexp.


(** **** Notations *)

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com. (* declare the scope of the new syntax. *)
Declare Scope com_scope.
Declare Custom Entry com_aux.

Notation "<{ e }>" := e (e custom com_aux) : com_scope.

Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x < y" := (BLt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNot (BEq x y)) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "x || y" := (BOr x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "x % y" := (AMod x y) (in custom com at level 40, left associativity).
Notation "x / y" := (ADiv x y) (in custom com at level 40, left associativity).

Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.

Open Scope com_scope.
Open Scope string_scope.
Open Scope nat_scope.

Definition imp_state := state nat.

Fixpoint ainterp (st : imp_state) (e: aexp) : nat :=
  match e with
  | ANum n => n
  | AId x => st x
  | APlus e1 e2 => (ainterp st e1) + (ainterp st e2)
  | AMinus e1 e2 => (ainterp st e1) - (ainterp st e2)
  | AMult e1 e2 => (ainterp st e1) * (ainterp st e2)
  | ADiv e1 e2 => div (ainterp st e1) (ainterp st e2)
  | AMod e1 e2 => (ainterp st e1) mod (ainterp st e2)   
  end.

Fixpoint binterp (st : imp_state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq e1 e2 => (ainterp st e1) =? (ainterp st e2)
  | BLe e1 e2 => (ainterp st e1) <=? (ainterp st e2)
  | BLt e1 e2 => (ainterp st e1) <? (ainterp st e2)
  | BNot b => negb (binterp st b)
  | BAnd b1 b2 => (binterp st b1) && (binterp st b2)
  | BOr b1 b2 =>  (binterp st b1) || (binterp st b2)
  end.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(** We extend the [com_scope] with notations for commands. *)
Notation "'skip'" :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90,
            right associativity) : com_scope.
Notation "{ x }" := x (in custom com, x at level 50) : com_scope.
Notation "'if' x 'then' y 'else' z" :=
         (CIf x y z)
           (in custom com at level 88, x at level 89,
            y at level 89, z at level 89) : com_scope.
Notation "'while' x 'do' y" :=
         (CWhile x y)
           (in custom com at level 88, x at level 89,
            y at level 89) : com_scope.

Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition RES : string := "RES".

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).


Inductive ceval : imp_state -> com -> imp_state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Asgn : forall st a n x,
      ainterp st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      binterp st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      binterp st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 ]=> st'
  | E_WhileFalse : forall b st c,
      binterp st b = false ->
      st =[ while b do c ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      binterp st b = true ->
      st =[ c ]=> st' ->
      st' =[ while b do c ]=> st'' ->
      st =[ while b do c ]=> st''

  where "st =[ c ]=> st'" := (ceval st c st').



Fixpoint cinterp (fuel : nat) (st : imp_state) (c : com) : option imp_state :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match c with
      | CSkip => Some st
      | CAsgn x n => Some (x !-> ainterp st n; st)
      | CSeq c1 c2 =>
          match cinterp fuel' st c1 with
          | Some st' => cinterp fuel' st' c2
          | None => None
          end
      | CIf b c1 c2 => if binterp st b then cinterp fuel' st c1 else cinterp fuel' st c2
      | CWhile b c =>
          if negb (binterp st b) then Some st (* If the condition is false, stop *) else
            match cinterp fuel' st c (* Run the body of the while once *) with
            | Some st' => cinterp fuel' st' (CWhile b c) (* Run the rest of the loop *)
            | None => None
            end
      end
  end.
