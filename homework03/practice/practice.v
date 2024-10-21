Require Import Coq.Lists.List Coq.Init.Nat Coq.Arith.Arith Coq.Strings.String Lia.

Require Import imp.

Set Warnings "-notation-overriden, -parsing".

(** * Practice Problems *)

(** ** Existential Quantifiers *)

(** Prove the division theorem. It states that for every natural
    number [m] and positive number [n] there exists unique [q] and [r]
    such that [m = q * n + r]. *)

(** First show the existence of such [q] and [r]. *)

Theorem division_theorem_existence :
  forall (m n : nat),
    n > 0 ->
    exists q r,
      m = q * n + r /\ r < n. 
Proof.
  intros m n Hnp.
  induction m.
  - exists 0, 0. lia.
  - destruct IHm as [q' IHm]. destruct IHm as [r' IHm].
    destruct IHm as [IHm H].
    rewrite IHm. rewrite plus_n_Sm with (n := q' * n) (m := r').
    destruct (Nat.eq_dec r' (n - 1)) as [Hr | Hr].
    + exists (S q'), 0. split; lia.
    + exists q', (S r'). split; lia.
Qed.

(** Note that the above proof provides an procedure for finding [q]
    and [r], i.e., an _algorithm_ euclidean division. We could in
    principle extract a computation from the above proof that returns
    [q] and [r]. Furthermore, we know that this computation is correct
    since we prove that [m = q * n + r].

    The above theorem is in essence a (recursive) function that:

    - takes as input an integer [m], an integer [n], a proof [n > 0]

    - Returns two integers [q] and [r] and a proof that [m = q * n + r /\ r < n].

    Q1: Is the above algorithm efficient?
    Q2: Why is the above theorem/function recursive?
        (Hint: See bonus question below)
*)

(** Then we can show the uniqueness of such representation. *)

Theorem division_theorem_uniqueness :
  forall (m n q1 q2 r1 r2: nat),
    n > 0 -> 
    m = q1 * n + r1 -> r1 < n ->
    m = q2 * n + r2 -> r2 < n ->
    q1 = q2 /\ r1 = r2.
Proof.
  intros m n q1 q2 r1 r2 Hmt H1 Hlt1 H2 Hlt2.
  assert (Hlt3: (q1 - q2) * n < n). lia.
  assert (Hlt4: (q2 - q1) * n < n). lia.
  destruct (q1 - q2) eqn: Heq1.
  destruct (q2 - q1) eqn: Heq2.
  - assert (Heq : q1 = q2). lia.
    split; lia.
  - simpl in *. lia. (** contradiction *)
  - simpl in *. lia. (** contradiction *)
Qed.

(** Bonus: Prove the induction principle on [nat]s by writing a
    recursive function. *)

Fixpoint my_nat_ind (P : nat -> Prop) (Hbase : P 0) (Hind : forall n, P n -> P (S n)) (n : nat) : P n :=
  match n with
  | 0 => Hbase
  | S n' => Hind n' (my_nat_ind P Hbase Hind n')
  end.

Check my_nat_ind. 

(** ** Delaying Instantiation of Quantifiers *)

(** Coq provides tactics that allow delayed instantiating of
    quantifiers.

    Such tactics are variations of known tactics that are written with
    a leading [e]:
    
    - [eapply]:

      apply an hypothesis/theorem without providing instances for all
      universal quantifiers.  For each universal quantifier that is
      are not instantiated during the application it introduces
      existential variables (evars) that must be unified before the
      proof ends.

    - [eassumption]:

      Similar to [assumption] by is able to unify evars. It will
      succeed even if the goal or the hypothesis have evars and will
      unify the evars with the corresponding terms.
      

    - [eexists]:

      Instead of providing a concrete witness for the existential,
      generate an evar that has to be instantiated with a concrete
      term before the end of the proof.
    
    - [eauto]

      Like [auto] but uses [eapply] and [eassumption].

    - [erewrite]

      Like rewrite, but if the hypothesis/theorem we are rewriting
      with has universal quantifiers, there instantiation can be
      delayed.

      
    There are two constraints when working with evars:

    1.) In order for [Qed] to succeed, there must not be any
        un-unified existential variables

    2.) Evars cannot be instantiated with terms containing variables
        that did not exist at the time the existential variable was
        created. *)


Lemma eapply_example :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (forall z y, P z y -> Q z) ->
    P 42 11 ->
    Q 42.
Proof.
  intros P Q HPQ HP.

  Fail apply HPQ.
  (* Coq cannot automatically find an instance for variable y, since
     it doesn't appear in the conclusion. So Coq, when unifying the conclusion
     of [HPQ] with the goal cannot come up with and instance of for [y]. *)
Abort.


Lemma eapply_example2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (forall z y, P z y -> Q z) ->
    (exists x, P 42 x) ->
    Q 42.
Proof.
  intros P Q HPQ HP.
  eapply HPQ. (* an evar ?y is introduced. *)

  destruct HP as [x HP].

  Fail eassumption. (* oops! [eassumption fails as [x] was not present in the context
                       when the [evar] was introduced] *)
Abort.

Lemma eapply_example2' :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (forall z y, P z y -> Q z) ->
    (exists x, P 42 x) ->
    Q 42.
Proof.
  intros P Q HPQ HP.
  destruct HP as [x HP].
  eapply HPQ.
  eassumption.
Qed.



Definition commutative {A} (P : A -> A -> Prop) := forall x y, P x y -> P y x.

Lemma eexists_example :
  forall A (x: A) P,
    commutative P ->
    (exists z, P x z) ->
    (exists z, P z x). 
Proof.
  intros A x P Hcom HP.
  eexists. 
  
  destruct HP as [z HP].
  apply Hcom.
  Fail eassumption. (* why? *)
Abort.


Lemma eexists_example' :
  forall A (x: A) P,
    commutative P ->
    (exists z, P x z) ->
    (exists z, P z x). 
Proof.
  intros A x P Hcom HP.
  destruct HP as [z HP].
  eexists.
  apply Hcom.
  eassumption.
Qed.



Lemma eapply_example3 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (forall z, P 42 z) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
  intros P Q HP HPQ.
  eapply HPQ.
  eapply HP.
Fail Qed. (* Why? *)
Abort.

Lemma eapply_example3' :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
    (forall z, P 42 z) ->
    (forall x y : nat, P x y -> Q x) ->
    Q 42.
Proof.
  intros P Q HP HPQ.
  eapply HPQ.
  eapply HP with (z := 17).
Qed.

  

(** ** Case study: Adding Nondeterministic Choice to [Imp] *)

(** In this exercise we wish to extend the commands of the [Imp]
    language with a nondeterministic choice operator when assigning
    values to variables. In particular, we extend the syntax with the
    construct

<<
<com> := ... | <var> ':=' <aexp> '|' <aexp>
>>

   Note: the syntax of the language is in quotes (e.g., '|', ':=') so that
   we can distinguish between the symbols of the syntax of the language and
   the symbols of the BNF grammar.

   For example, we can now write the assignment [<{ X := 3 | 4 }>]
   which can assign either [3] or [4] to [X]. *)

(** The semantics of the new assignment operator is that a variable
    gets the value of one the two arithmetic expression.

    The semantics does not specify how the choice is made (it can be
    done according to a some probability distribution, e.g., throwing
    a coin). It only specifies that picking any of the two values is
    possible *)

Module Nondet.

  (** Step 1: Extend the [com] AST with a case for nondeterministic choice. *)

  Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CAsgnChoice : string -> aexp -> aexp -> com.

  (** We redefine the notations and add notations or the new construct *)
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
  Notation "x := y | z" :=
    (CAsgnChoice x y z)
      (in custom com at level 0, x constr at level 0,
          y at level 85, z at level 85,
          no associativity) : com_scope.

  
  (** Step 2: Extend the semantics of [com] *)
  
  Reserved Notation
    "st '=[' c ']=>' st'"
    (at level 40, c custom com at level 99,
      st constr, st' constr at next level).


  Inductive ceval : imp_state -> com -> imp_state -> Prop :=
  | E_Skip : forall st,
      ceval st CSkip st
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
  | E_AsgnChoice_left : forall st al ar n x,
      ainterp st al = n ->
      st =[ x := al | ar ]=> (x !-> n ; st)
  | E_AsgnChoice_right : forall st al ar n x,
      ainterp st ar = n ->
      st =[ x := al | ar ]=> (x !-> n ; st)
                               
  where "st =[ c ]=> st'" := (ceval st c st').

  (** Step 3: Show that determinism no longer holds for the language.
      That is, show that there exists some program that can be
      executed twice on the same initial state resulting in different
      final states.

      We define two states [st1], [st2] to be different when there
      exists some variable [x] such that [st1 x <> st2 x]. *)

  Definition different (st1 st2: imp_state) :=
    exists z, st1 z <> st2 z.
  
  Lemma ceval_nondet:
    exists (c : com),
    forall (st : imp_state),
    exists (st1 st2 : imp_state),
        st =[ c ]=> st1 /\ st =[ c ]=> st2 /\ different st1 st2.
  Proof.
    exists (<{X := 10 | 15}>).

    intros st.
    eexists. eexists. repeat split.
    - eapply E_AsgnChoice_left. reflexivity.
    - eapply E_AsgnChoice_right. reflexivity.
    - exists X. intros H. discriminate H.
Qed.
    
  
End Nondet. 
