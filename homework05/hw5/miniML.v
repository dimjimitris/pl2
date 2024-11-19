Require Import Coq.Strings.String Coq.Init.Nat Lia List.

Import ListNotations.

Module MiniML.

  (** Binary Operators *)
  Inductive bop :=
  | Plus | Minus | Mult
  | And | Or | Lt | Eq.

  (** Unary Operators *)
  Inductive uop :=
  | Neg.

  (** The abstract syntax tree of miniML. *)
  Inductive term : Type :=
  (* Functions *)
  | T_App : term -> term -> term
  | T_Lambda : string -> term -> term
  (* Variables *)
  | T_Var : string -> term
  (* Natural Numbers *)
  | T_Nat : nat -> term
  (* Booleans *)
  | T_Bool : bool -> term
  (* Binary Operators *)
  | T_BOp : bop -> term -> term -> term
  (* Unary Operatos *)
  | T_UOp : uop -> term -> term
  (* Tuple *)
  | T_Tuple: list term -> term
  | T_Proj : nat -> term -> term
  (* Let *)
  | T_Let : string -> term -> term -> term
  (* If *)
  | T_If : term -> term -> term -> term
  .

  Declare Custom Entry ML.
  Declare Scope ML_scope.


  Notation "<[ e ]>" := e (e custom ML at level 99) : ML_scope.
  Notation "( x )" := x (in custom ML, x at level 99).
  Notation "x" := x (in custom ML at level 0, x constr at level 0).
  Notation "x y" := (T_App x y) (in custom ML at level 2, left associativity).

  Notation "'fun' x '->' y" := (T_Lambda x y) (in custom ML at level 90,
                                     x at level 99,
                                     y custom ML at level 99,
                                     left associativity) : ML_scope.

  Notation "'let' x ':=' y 'in' z" := (T_Let x y z) (in custom ML at level 90,
                                         x at level 99,
                                         y custom ML at level 100,
                                         z custom ML at level 100, left associativity) : ML_scope.

  Notation "'if' x 'then' y 'else' z" :=
    (T_If x y z)
      (in custom ML at level 89, x at level 99,
          y at level 99, z at level 99) : ML_scope.

  Notation "'true'" := true (at level 1).
  Notation "'true'" := (T_Bool true) (in custom ML at level 0).
  Notation "'false'" := false (at level 1).
  Notation "'false'" :=  (T_Bool false) (in custom ML at level 0).

  Notation "x <= y" := (T_BOp Or (T_BOp Lt x y) (T_BOp Eq x y))
                         (in custom ML at level 70, no associativity) : ML_scope.
  Notation "x < y" := (T_BOp Lt x y)
                        (in custom ML at level 70, no associativity) : ML_scope.
  Notation "x = y" := (T_BOp Eq x y)
                        (in custom ML at level 70, no associativity) : ML_scope.

  Notation "x <> y" := (T_UOp Neg (T_BOp Eq x y))
                         (in custom ML at level 70, no associativity) : ML_scope.

  Notation "x && y" := (T_BOp And x y) (in custom ML at level 80, left associativity) : ML_scope.
  Notation "x || y" := (T_BOp Or x y) (in custom ML at level 80, left associativity) : ML_scope.

  Notation "'~' b" := (T_UOp Neg b) (in custom ML at level 75, right associativity) : ML_scope.

  Notation "x + y" := (T_BOp Plus x y) (in custom ML at level 50, left associativity) : ML_scope.
  Notation "x - y" := (T_BOp Minus x y) (in custom ML at level 50, left associativity) : ML_scope.
  Notation "x * y" := (T_BOp Mult x y) (in custom ML at level 40, left associativity) : ML_scope.

  (* Notations for tuples *)
  Notation "'{' x ',' .. ',' y '}'" :=
    (T_Tuple (cons (x : term) .. (cons (y : term) []) ..))
      (in custom ML at level 0, (* TODO is this correct? *)
          x custom ML at level 99,
          y custom ML at level 99) : ML_scope.

  Notation "t '#' n " := (T_Proj n t)
                           (in custom ML at level 2,
                               n at level 99,
                               t custom ML,
                               left associativity) : ML_scope.

  Coercion T_Var : string >-> term.
  Coercion T_Nat : nat >-> term.

  Open Scope ML_scope.

  (** Some variables *)

  Definition f : string := "f".
  Definition foo : string := "for".
  Definition bar : string := "bar".
  Definition fact : string := "fact".
  Definition n : string := "n".
  Definition x : string := "x".
  Definition y : string := "y".

  (** The Z combinator is the strict version of the Y combinator. *)

  Definition Z := <[ fun f -> (fun x -> f (fun y -> x x y)) (fun x -> f (fun y -> x x y)) ]>.

  (** Notation for recursion using the Z combinator. *)

  Notation "'letrec' f ':=' y 'in' z" :=
    (T_Let f (T_App Z (T_Lambda f y)) z)
      (in custom ML at level 90,
          f at level 99,
          y custom ML at level 99,
          z custom ML at level 99) : ML_scope.

End MiniML.
