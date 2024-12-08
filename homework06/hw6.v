Require Import Coq.Strings.String Coq.Init.Nat Lia Coq.Lists.List.
Import List Notations.

(** Στοιχεία Σπουδαστή
Όνομα: ΔΗΜΗΤΡΙΟΣ ΓΕΩΡΓΟΥΣΗΣ
ΑΜ: 03119005
*)

(** * Εργασία 6: General Recursion (100 μονάδες + 20 μονάδες bonus **)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με τη στατική
    και δυναμική σημασιολογία του Λ λογισμού και των σχετικών
    επεκτάσεων καθώς και την απόδειξη ασφάλειας τύπων. 

    Οδηγίες:

    - Το παραδοτέο αρχείο θα πρέπει να κάνει compile. Τα αρχεία που
      δεν κάνουν compile δεν θα βαθμολογούνται.

    - Μην αλλάζετε τον κώδικα που σας έχει δοθεί. Μην γράφετε μέσα στα
      σχόλια της βαθμολόγησης. Αυτό είναι απαραίτητο για την ομαλή και
      έγκαιρη βαθμολόγηση των εργασιών. Μπορείτε να γράψετε όπου
      υπάρχει η οδηγία (* ___ FILL IN HERE ___ *). Εάν σας εξυπηρετεί,
      μπορείτε να ορίζετε βοηθητικές συναρτήσεις, λήμματα, ορισμούς,
      κ.α.

    - Μην αλλάζετε τα ονόματα των αρχείων. Γράψτε τις απαντήσεις σας
      μόνο σε αυτό το αρχείο.

    - Συμπληρώστε σωστά τα στοιχεία σας στην αρχή του αρχείου. Αυτό
      είναι απαραίτητο για τη σωστή βαθμολόγηση των εργασιών. *)



(** * Μέρος Α: Σημασιολογία και ασφάλεια τύπων. (60 μονάδες) *)


(** Όπως αναφέραμε στο μάθημα, η αναδρομή στο λ-λογισμό μπορεί να
    επιτευχθεί μέσω ενός fixed-point combinator, όπως ο Y ή ο
    Z. Ωστόσο, στο λ-λογισμό με απλούς τύπους, αυτοί οι combinators
    είναι ill-typed. Επιπλέον, λόγω της ιδιότητας του normalization, η
    γενική αναδρομή δεν μπορεί να επιτευχθεί ως παραγόμενη μορφή.

    Το πρώτο μέρος της άσκησης σας ζητά να προσθέσετε έναν primitive
    τελεστή fix στη γλώσσα, να ορίσετε τη στατική και τη δυναμική του
    σημασιολογία, και να επεκτείνετε την απόδειξη ασφάλειας τύπων.

    Σημείωση: Οι σημασιολογικοί ορισμοί για τον primitive τελεστή fix
    μπορούν να βρεθούν σε διάφορα textbooks γλωσσών προγραμματισμού
    (π.χ. στο Types and Programming Languages, ενότητα 11.11). Ωστόσο,
    συνιστάται να προσπαθήσετε να διατυπώσετε τους ορισμούς αυτούς
    μόνοι σας πριν ανατρέξετε στο βιβλίο.

    Το μεγαλύτερο μέρος του παρακάτω κώδικα προέρχεται αυτούσιο από
    τις σημειώσεις του μαθήματος (types.v). Σας ζητείται να
    συμπληρώσετε τους ορισμούς και τις αποδείξεις με τον τελεστή
    fix. Συμπληρώστε όπου υπάρχει η οδηγία [___ FILL IN HERE ___].

    Σημείωση: Οι αποδείξεις που δεν σας ζητείται να αλλάξετε
    αναμένεται να ολοκληρώνονται επιτυχώς ως έχουν, εφόσον οι ορισμοί
    σας είναι σωστοί. *)

(** The abstract syntax of types. *)

Inductive type : Type :=
| Arrow : type -> type -> type
| Nat   : type
| Bool  : type
| Unit  : type
| Sum   : type -> type -> type
| Prod  : type -> type -> type.

(** Binary Operators. *)

Inductive bop :=
(* arithmetic operatos *)
| Plus | Minus | Mult
(* boolan operators *)
| And | Or
(* comparison operators *)
| Lt | Eq.

(** Unary Operators. *)

Inductive uop :=
| Neg.

(** The abstract syntax of terms. *)

Inductive term : Type :=
(* Pure STLC fragment with functions, applications, and variables. *)
| T_App : term -> term -> term
| T_Lambda : string -> type -> term -> term
| T_Var : string -> term
(* Let *)
| T_Let : string -> term -> term -> term                      
(* Booleans *)
| T_Bool : bool -> term
(* If *)
| T_If : term -> term -> term -> term
(* Natural Numbers *)
| T_Nat : nat -> term
(* Binary Operators *)
| T_BOp : bop -> term -> term -> term
(* Unary Operatos *)
| T_UOp : uop -> term -> term
(* Pairs *)
| T_Pair : term -> term -> term
| T_Fst : term -> term
| T_Snd : term -> term
(* Sums *)
| T_Inl : type -> term -> term
| T_Inr : type -> term -> term
| T_Case : term -> string -> term -> string -> term -> term
(* Ο τελεστής Fix. Νέος όρος!!! *)
| T_Fix  : term -> term.

(** Concrete Syntax *)

Declare Scope ML_scope.

Declare Custom Entry ML.
Declare Custom Entry ML_ty.

Notation "<[ e ]>" := e (e custom ML at level 99) : ML_scope.
Notation "( x )" := x (in custom ML, x at level 99).
Notation "x" := x (in custom ML at level 0, x constr at level 0).


Notation "<[[ e ]]>" := e (e custom ML_ty at level 99) : ML_scope.
Notation "( x )" := x (in custom ML_ty, x at level 99).
Notation "x" := x (in custom ML_ty at level 0, x constr at level 0).

(** Types *)

Notation "S + T" := (Sum S T) (in custom ML_ty at level 3, left associativity).
Notation "X * Y" :=
  (Prod X Y) (in custom ML_ty at level 2, X custom ML_ty, Y custom ML_ty at level 0).
Notation "S -> T" := (Arrow S T) (in custom ML_ty at level 50, right associativity).

(** Terms *)

Notation "x y" := (T_App x y) (in custom ML at level 1, left associativity).

Notation "'fun'  x ':' T  '->' y" := (T_Lambda x T y) (in custom ML at level 90,
                                           x at level 99,
                                           T custom ML at level 99,
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

Notation "'inl' T t" := (T_Inl T t) (in custom ML at level 0,
                              T custom ML_ty at level 0,
                              t custom ML at level 0).
Notation "'inr' T t" := (T_Inr T t) (in custom ML at level 0,
                              T custom ML_ty at level 0,
                              t custom ML at level 0).
Notation "'case' t 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (T_Case t x1 t1 x2 t2) (in custom ML at level 89,
        t custom ML at level 99,
        x1 custom ML at level 99,
        t1 custom ML at level 99,
        x2 custom ML at level 99,
        t2 custom ML at level 99,
        left associativity).


Notation "( x ',' y )" := (T_Pair x y) (in custom ML at level 0,
                                x custom ML at level 99,
                                y custom ML at level 99).
Notation "t '.1'" := (T_Fst t) (in custom ML at level 1).
Notation "t '.2'" := (T_Snd t) (in custom ML at level 1).

Notation "'fix' t" := (T_Fix t) (in custom ML at level 0,
                            t custom ML at level 2).

(* antiquotation *)

Notation "{ x }" := x (in custom ML at level 1, x constr).

Coercion T_Var : string >-> term.
Coercion T_Nat : nat >-> term.
Coercion T_Bool : bool >-> term.

Open Scope ML_scope.

(** We define some commonly used variables. *)

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

(** ** Operational Semantics *)

(** *** Values *)

Inductive value : term -> Prop :=
(* Functions *)
| V_Fun :
  forall x T t,
    value <[ fun x : T -> t ]>
(* Natural Numbers *)
| V_Nat :
  forall (n : nat),
    value <[ n ]>
(* Booleans *)
| V_Bool :
  forall (b : bool),
    value <[ b ]>
(* Sums *)
| V_Inl : forall v T1,
    value v ->
    value <[ inl T1 v ]>
| V_Inr : forall v T1,
    value v ->
    value <[ inr T1 v ]>
(* Pairs *)
| V_Pair : forall v1 v2,
    value v1 ->
    value v2 ->
    value <[ (v1, v2) ]>.


(** *** Substitution. *)

Reserved Notation "'[' x ':=' s ']' t" (in custom ML at level 20, x constr).

Fixpoint subst (x : string) (t' : term) (t : term) : term :=
  match t with
  (* pure stlc *)
  | T_Var y =>
      if String.eqb x y then t' else t
  | <[ fun y : T -> t1 ]> =>
      if String.eqb x y then t else <[ fun y : T -> [x:=t']t1 ]>
  | <[ t1 t2 ]> =>
      <[ ([x:=t'] t1) ([x:=t'] t2) ]>
  (* nats and bools *)
  | T_Nat _ => t
  | T_Bool _ => t
  | T_BOp bop t1 t2 => T_BOp bop <[ [x:=t'] t1 ]>  <[ [x:=t'] t2 ]>
  | T_UOp uop t1 => T_UOp uop <[ [x:=t'] t1 ]> 
  | <[ if t1 then t2 else t3 ]> =>
      <[ if [x := t'] t1 then [x := t'] t2 else [x := t'] t3 ]>
  (* pairs *)
  | <[ (t1, t2) ]> => <[ ([x:=t'] t1, [x:=t'] t2) ]>
  | <[ t.1 ]> => <[ ([x:=t'] t).1 ]>
  | <[ t.2 ]> => <[ ([x:=t'] t).2 ]>
  (* sums *)
  | <[ inl T2 t1 ]> =>
      <[ inl T2 ([x:=t'] t1) ]>
  | <[ inr T1 t2 ]> =>
      <[ inr T1 ( [x:=t'] t2) ]>
  | <[ case t of | inl y1 => t1 | inr y2 => t2 ]> =>
      let t1' := if String.eqb x y1 then t1 else <[ [x:=t'] t1 ]> in
      let t2' := if String.eqb x y2 then t2 else <[ [x:=t'] t2 ]> in
      <[ case ([x:=t'] t) of
         | inl y1 => t1'
         | inr y2 => t2' ]>        
  | <[ let y := t1 in t2 ]> =>
      let t2' := if String.eqb x y then t2 else <[ [x:=t'] t2 ]> in
      <[ let y := [x:=t'] t1 in t2' ]>
  (* Ορισμός αντικατάστασης για τον τελεστή fix. *)
  | <[ fix t ]> => <[ fix ([x:=t'] t)  ]>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom ML).


Reserved Notation "t '-->' t'" (at level 40).

(** Helper functions to distinguish between operators of different
    types and define their interpretation. *)

Definition is_nat_op (op : bop) : bool :=
  match op with
  | Plus | Minus | Mult => true
  | _ => false
  end.

Definition nat_op (op : bop) : option (nat -> nat -> nat) :=
  match op with
  | Plus => Some add
  | Minus => Some sub
  | Mult => Some mul
  | _ => None
  end.

Definition is_bool_op (op : bop) : bool :=
  match op with
  | And | Or => true
  | _ => false
  end.

Definition bool_op (op : bop) : option (bool -> bool -> bool) :=
  match op with
  | And => Some andb
  | Or => Some orb
  | _ => None
  end.

Definition is_cmp_op (op : bop) : bool :=
  match op with
  | Eq | Lt => true
  | _ => false
  end.

Definition cmp_op (op : bop) : option (nat -> nat -> bool) :=
  match op with
  | Eq => Some eqb
  | Lt => Some ltb
  | _  => None
  end.

(** Call-by-value reduction relation *)
Inductive step : term -> term -> Prop :=
(* pure STLC *)
| Step_AppAbs : forall x T2 t1 v2,
    value v2 ->
    <[ (fun x:T2 -> t1) v2 ]> --> <[ [x:=v2]t1 ]>
| Step_App1 : forall t1 t1' t2,
    t1 --> t1' ->
    <[ t1 t2 ]> --> <[ t1' t2 ]>
| Step_App2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    <[ v1 t2 ]> --> <[ v1 t2' ]>
(* Let *)
| Step_LetVal : forall y v1 t2,
    value v1 ->
    <[ let y := v1 in t2 ]> --> <[ [y := v1] t2 ]>
| Step_Let : forall y t1 t1' t2,
    t1 --> t1'  ->
    <[ let y := t1 in t2 ]> --> <[ let y := t1' in t2 ]>
(* If then else *)
| Step_IfTrue : forall t1 t2,
    <[ if true then t1 else t2 ]> --> t1
| Step_IfFalse : forall t1 t2,
    <[ if false then t1 else t2 ]> --> t2
| Step_If: forall t t' t1 t2,
    t --> t' ->
    <[ if t then t1 else t2 ]> --> <[ if t' then t1 else t2 ]>
(* Binary Operators *)
| Step_BOpNat :
  forall bop (n1 n2 : nat) bop_f,
    nat_op bop = Some bop_f -> 
    (T_BOp bop n1 n2) --> T_Nat (bop_f n1 n2)
| Step_BOpBool :
  forall bop (b1 b2 : bool) bop_f,
    bool_op bop = Some bop_f -> 
    (T_BOp bop b1 b2) --> T_Bool (bop_f b1 b2)
| Step_BOpCmp :
  forall bop (n1 n2 : nat) bop_f,
    cmp_op bop = Some bop_f -> 
    (T_BOp bop n1 n2) --> T_Bool (bop_f n1 n2)
| Step_Bop1 : forall bop t1 t1' t2,
    t1 --> t1' ->
    (T_BOp bop t1 t2) --> (T_BOp bop t1' t2)  
| Step_Bop2 : forall bop v1 t2 t2',
    value v1 ->    
    t2 --> t2' ->
    (T_BOp bop v1 t2) --> (T_BOp bop v1 t2')
(* Unary Operators *)
| Step_UOpBool : forall (b : bool),
    (T_UOp Neg b) --> T_Bool (negb b)
| Step_UOp : forall t t',
    t --> t' ->
    (T_UOp Neg t) --> (T_UOp Neg t')
(* Pairs *)
| Step_Pair1 : forall t1 t1' t2,
    t1 --> t1' ->
    <[ (t1, t2) ]> --> <[ (t1', t2) ]>
| Step_Pair2 : forall v1 t2 t2',
    value v1 ->
    t2 --> t2' ->
    <[ (v1, t2) ]> --> <[ (v1, t2') ]>
| Step_FstPair : forall v1 v2, 
    value v1 -> value v2 ->
    <[ (v1, v2).1 ]> --> <[ v1 ]>
| Step_Fst : forall t t', 
    t --> t' ->
    <[ t.1 ]> --> <[ t'.1 ]>
| Step_SndPair : forall v1 v2, 
    value v1 -> value v2 ->
    <[ (v1, v2).2 ]> --> <[ v2 ]>
| Step_Snd : forall t t', 
    t --> t' ->
    <[ t.2 ]> --> <[ t'.2 ]>
(* Sums *)
| Step_Inl : forall t1 t1' T2,
    t1 --> t1' ->
    <[ inl T2 t1 ]> --> <[ inl T2 t1' ]>
| Step_Inr : forall t2 t2' T1,
    t2 --> t2' ->
    <[ inr T1 t2 ]> --> <[ inr T1 t2' ]>
| Step_Case : forall t t' x1 t1 x2 t2,
    t --> t' ->
    <[ case t of | inl x1 => t1 | inr x2 => t2 ]> -->
    <[ case t' of | inl x1 => t1 | inr x2 => t2 ]>
| Step_CaseInl : forall v x1 t1 x2 t2 T2,
    value v ->
    <[ case inl T2 v of | inl x1 => t1 | inr x2 => t2 ]> --> <[ [x1:=v]t1 ]>
| Step_CaseInr : forall v x1 t1 x2 t2 T1,
    value v ->
    <[ case inr T1 v of | inl x1 => t1 | inr x2 => t2 ]> --> <[ [x2:=v]t2 ]>
(* Fix *)
| Step_FixAbs : forall t x T,
    <[ fix (fun x : T -> t) ]> --> <[ [x := (fix (fun x : T -> t))] t ]>
| Step_Fix : forall t t',
    t --> t' ->
    <[ fix t ]> --> <[ fix t' ]>

(* [step] grade 0/20 *)
      
where "t '-->' t'" := (step t t').

(** ** Typing *)

(** Environments. *)

Definition partial_map A := string -> option A.

Definition empty {A : Type} : partial_map A :=
  fun _ => None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  fun x' => if String.eqb x x' then Some v else m x'.

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition context := string -> option type.

Reserved Notation "Gamma '⊢' t ':' T" (at level 40, t custom ML, T custom ML_ty at level 0).

(* The typing relation *)
Inductive has_type : context -> term -> type -> Prop :=
  (* Pure STLC *)
  | Ty_Var : forall Gamma x A,
      Gamma x = Some A ->
      Gamma ⊢ x : A
  | Ty_Abs : forall Gamma x t A B ,
      (x |-> A ; Gamma) ⊢ t : B ->
      Gamma ⊢ (fun x : A -> t) : (A -> B)
  | Ty_App : forall Gamma t1 t2 A B,
      Gamma ⊢ t1 : (A -> B) ->
      Gamma ⊢ t2 : A ->
      Gamma ⊢ t1 t2 : B
  (* Let *)
  | Ty_Let : forall Gamma x t1 t2 A B,
      Gamma ⊢ t1 : A ->
      (x |-> A ; Gamma) ⊢ t2 : B ->
      Gamma ⊢ (let x := t1 in t2) : B
  (* Bools *)
  | Ty_Bool : forall Gamma (b : bool),
      Gamma ⊢ b : Bool
  | Ty_If : forall Gamma t1 t2 t3 A,
      Gamma ⊢ t1 : Bool ->
      Gamma ⊢ t2 : A ->
      Gamma ⊢ t3 : A ->
      Gamma ⊢ if t1 then t2 else t3 : A
  | Ty_BopBool : forall Gamma bop t1 t2,
      Gamma ⊢ t1 : Bool ->
      Gamma ⊢ t2 : Bool ->
      is_bool_op bop = true ->
      Gamma ⊢ { T_BOp bop t1 t2 } : Bool
  | Ty_UOp : forall Gamma uop t1,
      Gamma ⊢ t1 : Bool ->
      Gamma ⊢ { T_UOp uop t1 } : Bool
  (* Numbers *)
  | Ty_Nat : forall Gamma (n : nat),
      Gamma ⊢ n : Nat
  | Ty_BopNat : forall Gamma bop t1 t2,
      Gamma ⊢ t1 : Nat ->
      Gamma ⊢ t2 : Nat ->
      is_nat_op bop = true ->
      Gamma ⊢ { T_BOp bop t1 t2 } : Nat
  | Ty_BopCmp : forall Gamma bop t1 t2,
      Gamma ⊢ t1 : Nat ->
      Gamma ⊢ t2 : Nat ->
      is_cmp_op bop = true ->
      Gamma ⊢ { T_BOp bop t1 t2 } : Bool
  (* Pairs *)
  | Ty_Pair : forall Gamma t1 t2 A B,
      Gamma ⊢ t1 : A ->
      Gamma ⊢ t2 : B ->
      Gamma ⊢ (t1, t2) : (A * B)
  | Ty_Fst : forall Gamma t1 A B,
      Gamma ⊢ t1 : (A * B) ->
      Gamma ⊢ t1.1 : A
  | Ty_Snd : forall Gamma t1 (A B : type),
      Gamma ⊢ t1 : (A * B) ->
      Gamma ⊢ t1.2 : B
  (* Sums *)
  | Ty_Inl : forall Gamma t1 A B,
      Gamma ⊢ t1 : A ->
      Gamma ⊢ (inl B t1) : (A + B)
  | Ty_Inr : forall Gamma t2 A B,
      Gamma ⊢ t2 : B ->
      Gamma ⊢ (inr A t2) : (A + B)
  | Ty_Case : forall Gamma t x1 A t1 x2 B t2 C,
      Gamma ⊢ t : (A + B) ->
      (x1 |-> A ; Gamma) ⊢ t1 : C ->
      (x2 |-> B ; Gamma) ⊢ t2 : C ->
      Gamma ⊢ (case t of | inl x1 => t1 | inr x2 => t2) : C
  (* Fix *)
  | Ty_Fix : forall Gamma t A,
      Gamma ⊢ t : (A -> A) ->
      Gamma ⊢ (fix t) : A
      
where "Gamma '⊢' t ':' T" := (has_type Gamma t T).


(* [has_type] grade 0/10*)

(** We extend the auto core database with the constructors of the
    [value], [step] and [has_type] relations. *)

Hint Constructors value : core.
Hint Constructors step : core.
Hint Constructors has_type : core.

(** ** Type Safety **)

Ltac inv H := inversion H; clear H; subst.

(** *** Canonical Forms *)

Lemma canonical_forms_bool :
  forall t,
    empty ⊢ t : Bool ->
    value t ->
    (t = <[ true ]>) \/ (t = <[ false ]>).
Proof.
  intros t Htyp Hval.
  inv Hval; inv Htyp.
  destruct b; auto.
Qed.

Lemma canonical_forms_nat :
  forall t,
    empty ⊢ t : Nat ->
    value t ->
    exists (n : nat), t = <[ n ]>.
Proof.
  intros t Htyp Hval.
  inv Hval; inv Htyp. eauto.
Qed.

Lemma canonical_forms_fun :
  forall t T1 T2,
    empty ⊢ t : (T1 -> T2) ->
    value t ->
    exists x u, t = <[ fun x : T1  -> u ]>.
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp. eauto.
Qed.

Lemma canonical_forms_sum :
  forall t T1 T2,
    empty ⊢ t : (T1 + T2) ->
    value t ->
    (exists t1, t = <[ inl T2 t1 ]> /\ value t1) \/
    (exists t2, t = <[ inr T1 t2 ]> /\ value t2).
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp; eauto.
Qed.

Lemma canonical_forms_prod :
  forall t T1 T2,
    empty ⊢ t : (T1 * T2) ->
    value t ->
    exists t1 t2, t = <[ (t1, t2) ]> /\ value t1 /\ value t2.
Proof.
  intros t T1 T2 Htyp Hval.
  inv Hval; inv Htyp; eauto.
Qed.

(** Helper lemmas for binary operators *)

Lemma is_nat_op_lemma :
  forall bop, is_nat_op bop = true -> exists f, nat_op bop = Some f. 
Proof. intros []; simpl; try discriminate; eauto. Qed.

Lemma is_bool_op_lemma :
  forall bop, is_bool_op bop = true -> exists f, bool_op bop = Some f. 
Proof. intros []; simpl; try discriminate; eauto. Qed.

Lemma is_cmp_op_lemma :
  forall bop, is_cmp_op bop = true -> exists f, cmp_op bop = Some f. 
Proof. intros []; simpl; try discriminate; eauto. Qed.

(** *** Progress *)

(** Note: Proof of certain cases and comments are taken from "Software
    Foundations"*)

(** Theorem: Suppose empty ⊢- t \in A.  Then either
      1. t is a value, or
      2. t --> t' for some t'.

    Proof: By induction on the given typing derivation. *)

Theorem progress : forall t T,
     empty ⊢ t : T ->
     value t \/ exists t', t --> t'.
Proof.
  intros t T Ht.
  remember empty as Gamma.
  induction Ht; subst.
  - (* Ty_Var *)
    (* The final rule in the given typing derivation cannot be
       [Tt_Var], since it can never be the case that
       [empty ⊢ x : T] (since the context is empty). *)
    discriminate H.    
  - (* Ty_Abs *)
    (* If the [Ty_Abs] rule was the last used, then
       [t = fun x0 : T2 -> t1], which is a value. *)
    now left.
    
  - (* Ty_App *)
    
    (* If the last rule applied was Ty_App, then [t = t1 t2],
       and we know from the form of the rule that
         [empty ⊢ t1 : T1 -> T2]
         [empty ⊢ t2 : T1]
       By the induction hypothesis, each of t1 and t2 either is
       a value or can take a step. *)
    right.
    
    destruct IHHt1.
    + reflexivity.
    + (* t1 is a value *)
      destruct IHHt2.
      * reflexivity.
      * (* t2 is a value *)
        (* If both [t1] and [t2] are values, then we know that
           [t1 = fun x0 : T0 -> t11], since abstractions are the
           only values that can have an arrow type.  But
           [(fun x0 : T0 -> t11) t2 --> [x:=t2]t11] by [Step_AppAbs]. *)
        eapply canonical_forms_fun in Ht1; [| assumption ].

        destruct Ht1 as [x [u Heq]]; subst.
        eauto.        
      * (* t2 steps *)
        (* If [t1] is a value and [t2 --> t2'],
           then [t1 t2 --> t1 t2'] by [Step_App2]. *)
        destruct H0 as [t2' Hstp].        
        exists <[t1 t2']>; auto.
    + (* t1 steps *)
      (* Finally, If [t1 --> t1'], then [t1 t2 --> t1' t2]
         by [Step_App1]. *)
      destruct H as [t1' Hstp]. exists <[t1' t2]>; auto.
  - (* Ty_let *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ]. 
  - (* Ty_Bool *)
    eauto.

  - (* TY_If *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ].

    edestruct (canonical_forms_bool t1); subst; eauto.

  - (* Ty_Bop bool *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct is_bool_op_lemma; eauto.

    edestruct (canonical_forms_bool t1); eauto; subst;
    edestruct (canonical_forms_bool t2); eauto; subst; eauto.

  - (* T_Uop bool *)
    destruct uop0.
    destruct IHHt as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto]. 
     
    edestruct (canonical_forms_bool t1); eauto; subst; eauto.

  - (* Ty_Nat *)
    left; auto.
  - destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct (canonical_forms_nat t1); eauto; subst.
    edestruct (canonical_forms_nat t2); eauto; subst.

    edestruct is_nat_op_lemma; eauto.

  - (* Ty_Bop cmp *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    edestruct (canonical_forms_nat t1); eauto; subst.
    edestruct (canonical_forms_nat t2); eauto; subst.

    edestruct is_cmp_op_lemma; eauto.

  - (* Ty_Pair *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ]. 
    destruct IHHt2 as [ | [t2' Hstp]];
      subst; [ reflexivity | | now eauto ]. 

    eauto.
    
  - (* Ty_fst *)
    destruct IHHt as [ | [t' Hstp]];
      subst; [ reflexivity | | now eauto ].
    edestruct (canonical_forms_prod t1) as [ v1 [v2 [Hstp1 [Hv1 Hv2]]]]; eauto.
    subst; eauto.

  - (* Ty_snd *)
    destruct IHHt as [ | [t' Hstp]];
      subst; [ reflexivity | | now eauto ].
    edestruct (canonical_forms_prod t1) as [ v1 [v2 [Hstp1 [Hv1 Hv2]]]]; eauto.
    subst; eauto.

  - (* Ty_Inl *)
    destruct IHHt as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ]. 

  - (* Ty_Inr *)
    destruct IHHt as [ | [t1' Hstp]];
      subst; [ reflexivity | now eauto | now eauto ].

  - (* Ty_case *)
    destruct IHHt1 as [ | [t1' Hstp]];
      subst; [ reflexivity | | now eauto ].

    edestruct (canonical_forms_sum t) as [ [v1 [Hstp1 Hv1]] | [v2 [Hstp2 Hv2]]];
      eauto; subst; eauto.

  - (* Ty_fix *)
    destruct IHHt as [ | [t' Hstp]]; eauto.
    edestruct (canonical_forms_fun t) as [x [u Hstp]];
    [ | | try rewrite Hstp]; eauto.
Qed.

(* [progress] grade 0/10*)


(** *** Weakening *)

Definition submap {A : Type} (m m' : partial_map A) : Prop :=
  forall x v, m x = Some v -> m' x = Some v.

(** We prove some useful lemmas for maps and the submap relation. *)

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite eqb_refl. reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update.
  apply eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma submap_update :
  forall (A : Type) (m m' : partial_map A) (x : string) (vx : A),
  submap m m' ->
  submap (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold submap.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_spec x y) as [Hxy | Hxy].
  - rewrite Hxy.
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq.
    + rewrite update_neq.
      * apply H.
      * apply Hxy.
    + apply Hxy.
Qed.


(** Weakening follows easily by induction on the typing derivation. *)

Lemma weakening :
  forall Gamma Gamma' t A,
    submap Gamma Gamma' ->
    Gamma  ⊢ t : A  ->
    Gamma' ⊢ t : A.
Proof.
  intros Gamma Gamma' t  A Hsub Ht.
  revert Gamma' Hsub.
  induction Ht; eauto 7 using submap_update.
Qed.

Corollary weakening_empty :
  forall Gamma t A,
    empty ⊢ t : A  ->
    Gamma ⊢ t : A.
Proof.
  intros Gamma t A.
  eapply weakening.
  discriminate.
Qed.


(** *** Substitution Preserves Typing *)

Require Import Coq.Logic.FunctionalExtensionality. 

Check functional_extensionality.

Lemma update_shadow :
  forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x y); subst; eauto.
Qed.

Lemma update_same :
  forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x y); subst; eauto.
Qed.

Lemma update_permute :
  forall (A : Type) (m : partial_map A) x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2 Hneq. unfold update.
  apply functional_extensionality. intros y.
  destruct (eqb_spec x1 y); subst; eauto.
  destruct (eqb_spec x2 y); subst; eauto.
  congruence. 
Qed.

(** Substitution preserves typing lemma. *)

Lemma substitution_preserves_typing :
  forall Gamma x v t A B,
    (x |-> B ; Gamma) ⊢ t : A ->
    empty ⊢ v : B   ->
    Gamma ⊢ [x:=v]t : A.
Proof.
  intros Gamma x v t A B Ht Hv.
  revert Gamma A Ht Hv. 
  induction t; intros Gamma A Ht1 Ht2; inv Ht1; simpl; eauto.
  - (* T_Abs *)
    destruct (eqb_spec x s); subst; apply Ty_Abs.
    + (* x = s *)
      rewrite update_shadow in H4. assumption.
    + (* x <> s *)
      apply IHt; auto.
      rewrite update_permute; auto.

  - (* T_Var *)
    destruct (eqb_spec x s); subst.
    + (* x = s *)
      rewrite update_eq in H1. inv H1. 
      apply weakening_empty. assumption.
    + (* x <> y *)
      apply Ty_Var. rewrite update_neq in H1; auto.

  - (* T_let *)
    eapply Ty_Let.
    + eapply IHt1; eauto.
    + destruct (eqb_spec x s); subst.
      * (* x = s *)        
        rewrite update_shadow in H5. assumption.
      * (* x <> s *)        
        eapply IHt2; auto.
        rewrite update_permute; eauto.
  - (* T_Case *)
    eapply Ty_Case.
    + now eauto.
    + destruct (eqb_spec x s); subst.
      * (* x = s *)
        rewrite update_shadow in H7. assumption.
      * (* x <> s *)
        apply IHt2.
        rewrite update_permute; auto.
        assumption.
    + destruct (eqb_spec x s0); subst.
      * (* x = s0 *)
        rewrite update_shadow in H8. assumption.
      * (* x <> s0 *)
        apply IHt3.
        rewrite update_permute; auto.
        assumption.
Qed.

(** *** Preservation *)

(** We can now prove the preservation theorem. *)

Theorem preservation :
  forall t t' A,
    empty ⊢ t : A  ->
    t --> t'  ->
    empty ⊢ t' : A.
Proof.
  intros t t' A Htyp. revert t'.
  remember empty as Gamma.
  induction Htyp; intros t' Hstep; subst.
  - (* Ty_Var *)
    inv Hstep.
  - (* Ty_Abs *)
    inv Hstep.
  - (* Ty_App *)
    inv Hstep.
    inv Htyp1.
    + eapply substitution_preserves_typing; eauto.
    + eauto.
    + eauto.

  - (* Ty_Let *)
    inv Hstep; eauto.
    eapply substitution_preserves_typing; eauto.

  - (* Ty_Bool *)
    inv Hstep.

  - (* Ty_If *)
    inv Hstep; eauto.

  - (* Ty_Bop *)
    inv Hstep; eauto.
    
    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_UOp *)
    inv Hstep; eauto.

  - (* Ty_Nat *)
    inv Hstep.

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_Bop *)
    inv Hstep; eauto.

    now destruct bop0; simpl in *; try congruence. (* TODO nicer *)

  - (* Ty_Pair *)
    inv Hstep; eauto.

  - (* Ty_Fst *)
    inv Hstep; eauto.
    
    inv Htyp; eauto. 

  - (* Ty_Snd *)
    inv Hstep; eauto.
    
    inv Htyp; eauto. 

  - (* Ty_inl *)
    inv Hstep; eauto.
    
  - (* Ty_inr *)
    inv Hstep; eauto.
    
  - (* Ty_case *)
    inv Hstep; eauto.
    + inv Htyp1.
      eapply substitution_preserves_typing; eauto.
    + inv Htyp1. 
      eapply substitution_preserves_typing; eauto.

  - (* Ty_fix *)
    inv Hstep; eauto.
    eapply substitution_preserves_typing; eauto.
    inv Htyp; eauto.
Qed. 


(* [preservation] grade 0/10*)

(** ** Type Checking *)

(** Lastly, we define a typechecking program that we prove sound and
    complete with respect to our typing relation. *)


(** First, we define equality on types by recursion on their
    structure. *)
Fixpoint ty_eqb (A B: type) : bool :=
  match A, B with
  | Bool, Bool => true
  | Nat, Nat => true
  | Unit, Unit => true
  | <[[ A1 -> A2 ]]>, <[[ B1 -> B2 ]]> =>
      andb (ty_eqb A1 B1) (ty_eqb A2 B2)
  | <[[ A1 + A2 ]]>, <[[ B1 + B2 ]]> =>
      andb (ty_eqb A1 B1) (ty_eqb A2 B2)
  | <[[ A1 * A2 ]]>, <[[ B1 * B2 ]]> =>
      andb (ty_eqb A1 B1) (ty_eqb A2 B2)
  | _, _ => false
  end.

(** Monadic notations. *)

Notation "x <- e1 ;; e2" := (match e1 with
                             | Some x => e2
                             | None => None
                              end)
         (right associativity, at level 60).

Notation " 'return' e " := (Some e) (at level 60).

Notation " 'fail' " := None.


Fixpoint type_check (Gamma : context) (t : term) : option type :=
  match t with
  (*  Pure STLC *)
  | T_Var x => Gamma x
  | <[ fun x : A -> t1 ]> =>
      B <- type_check (x |-> A ; Gamma) t1 ;;
      return <[[ A -> B ]]>
  | <[ t1 t2 ]> =>
      A <- type_check Gamma t1 ;;
      B <- type_check Gamma t2 ;;
      match A with
      | <[[ A1 -> A2 ]]> =>
          if ty_eqb A1 B then return A2 else fail
      | _ => fail
      end
  (* Let *)
  | <[ let y := t1 in t2 ]> =>
      A <- type_check Gamma t1 ;;
      type_check (y |-> A ; Gamma) t2
  (* Booleans *)
  | T_Bool _ => return <[[ Bool ]]>
  | <[ if b then t1 else t2 ]> =>
      A <- type_check Gamma b ;;
      B <- type_check Gamma t1 ;;
      C <- type_check Gamma t2 ;;
      match A with
      | <[[ Bool ]]> => if ty_eqb B C then return B else fail
      | _ => fail
      end
  (* Numbers *)
  | T_Nat n => return <[[ Nat ]]>    
  (* Binary operators *)
  | T_BOp bop t1 t2 =>
      A <- type_check Gamma t1 ;;
      B <- type_check Gamma t2 ;;
      if ty_eqb A B then 
        if is_nat_op bop then
          if ty_eqb A Nat then return Nat else fail
        else if is_cmp_op bop then
          if ty_eqb A Nat then return Bool else fail
        else if is_bool_op bop then
          if ty_eqb A Bool then return Bool else fail
        else fail
      else fail
  (* Unary operators *)
  | T_UOp b t1 =>
      A <- type_check Gamma t1 ;;
      if ty_eqb A Bool then return Bool else fail
  (* Pairs *)
  | <[ (t1, t2)]> =>
      A <- type_check Gamma t1 ;;
      B <- type_check Gamma t2 ;;
      return <[[ A * B ]]>
  | <[ t1.1 ]> =>
      A <- type_check Gamma t1 ;;
      match A with
      | <[[ A1 * A2 ]]> => return A1
      | _ => fail
      end
  | <[ t1.2 ]> =>
      A <- type_check Gamma t1 ;;
      match A with
      | <[[ A1 * A2 ]]> => return A2
      | _ => fail
      end
  (* Sums *)
  | <[ inl B t1 ]> =>
      A <- type_check Gamma t1 ;;
      return <[[ A + B ]]>
  | <[ inr A t1 ]> =>
      B <- type_check Gamma t1 ;;
      return <[[ A + B ]]>
  | <[ case t of | inl y1 => t1 | inr y2 => t2 ]> =>
      A <- type_check Gamma t ;;
      match A with
      | <[[ A1 + A2 ]]> =>
          B <- type_check (y1 |-> A1 ; Gamma) t1 ;; 
          C <- type_check (y2 |-> A2 ; Gamma) t2 ;;
          if ty_eqb B C then return B else fail
      | _ => fail
      end
  (* Fix *)
  | <[ fix t ]> =>
      A <- type_check Gamma t ;;
      match A with
      | <[[ A1 -> A2 ]]> =>
          if ty_eqb A1 A2 then return A1 else fail
      | _ => fail
      end
  end.

(* [type_check] grade 0/10*)

(** *** Correctness of Type Checking *)

(** We first prove some simple lemmas about type equality. *)

Lemma ty_eqb_eq :
  forall t1 t2, ty_eqb t1 t2 = true -> t1 = t2.
Proof.
  induction t1; intros []; simpl; intros H; try congruence.
  - apply andb_prop in H. destruct H.
    erewrite IHt1_1; eauto.
    erewrite IHt1_2; eauto.
  - apply andb_prop in H. destruct H.
    erewrite IHt1_1; eauto.
    erewrite IHt1_2; eauto.
  - apply andb_prop in H. destruct H.
    erewrite IHt1_1; eauto.
    erewrite IHt1_2; eauto.
Qed.    

Lemma ty_eqb_refl :
  forall t, ty_eqb t t = true.
Proof.
  induction t; simpl; auto.
  - rewrite IHt1; eauto.
  - rewrite IHt1; eauto.
  - rewrite IHt1; eauto.
Qed.    


Ltac simpl_tc :=
  match reverse goal with
  | [H: ty_eqb ?t1 ?t2 = true |- _] => apply ty_eqb_eq in H; subst
  | [H: Some _ = Some _ |- _] => inv H
  | [_ : match ?t with _ => _ end = _ |- _] =>
      destruct t eqn:?; try congruence
  | [_: context[ty_eqb ?t1 ?t2] |- _] =>
      destruct (ty_eqb t1 t2) eqn:?; subst; try congruence
  end.

(** Soundness. *)

Theorem type_checking_sound :
  forall Gamma t A,
    type_check Gamma t = Some A ->
    Gamma ⊢ t : A.
Proof.
  intros Gamma t. revert Gamma.
  induction t; intros Gamma A Htc; simpl in *;
    try now (repeat simpl_tc; eauto).
Qed.

(** Completeness. *)

Theorem type_checking_complete :
  forall Gamma t A,
    Gamma ⊢ t : A ->
    type_check Gamma t = Some A.
Proof.
  intros Gamma t A Htyp; induction Htyp; simpl; eauto;
  try rewrite IHHtyp; try rewrite IHHtyp1; try rewrite IHHtyp2;
    try rewrite IHHtyp3;
    try rewrite ty_eqb_refl; try reflexivity.
  
  - destruct bop0; simpl in *; try congruence.
  - destruct bop0; simpl in *; try congruence.
  - destruct bop0; simpl in *; try congruence.    
Qed.


(** * Μέρος Β: Παραγόμενες Μορφές. (40 μονάδες + 20 μονάδες bonus) *)

(** Το δεύτερο μέρος της άσκησης σας ζητάει να ορίσετε το [let rec
    ... in ...] (αναδρομικές συναρτήσεις) και το [let rec ... and
    ... in ..] (αμοιβαία αναδρομικές συναρτήσεις) ως παραγόμενες
    μορφές (syntactic sugar). *)


(** ** Αναδρομικές συναρτήσεις μέσω της δομής [let rec]. *)

(** Σύνταξη: [let rec f = t1 in t2] όπου το f μπορεί να εμφανίζεται
    μέσα στον ορισμό του.

    Hint: Δείτε το notation που έχουμε ορίσει για το let-rec στην
    untyped miniML. *)

Definition letrec (f : string) (fA : type) (ft : term) (rest : term) : term :=
  <[ let f := (fix (fun f : fA -> ft)) in rest ]>.


(* [letrec] grade 0/10 *)

Notation "'let' 'rec' f ':' T ':=' y 'in' z" :=
  (letrec f T y z)
    (in custom ML at level 90,
        f at level 99,
        T custom ML_ty at level 99,
        y custom ML at level 99,
        z custom ML at level 99) : ML_scope.


(** ** Aμοιβαία αναδρομικές συναρτήσεις μέσω της δομής [let rec ... and]. *)

(** Σύνταξη: [let rec f = t1 and g = t3 in t3] όπου το [f] και το [g]
    μπορούν να εμφανίζονται αναδρομικά μέσα στους ορισμούς τους [t1]
    και [t2].

    Σημείωση: Αν και η άσκηση σας ζητά να ορίσετε μια δομή με μόνο δύο
    αμοιβαία αναδρομικές συναρτήσεις, η δομή μπορεί να γενικευτεί ώστε
    να επιτρέπει τον ορισμό οποιουδήποτε αριθμού αμοιβαία αναδρομικών
    συναρτήσεων. *)

Definition _arg : string := "_arg".
Definition h : string := "h".

Definition letrecand (f : string) (fA : type) (ft : term)
                     (g : string) (gA : type) (gt : term)
                     (rest : term) : term :=
<[
    let rec f : fA := let rec g : gA := gt in ft in
    let rec g : gA := let rec f : fA := ft in gt in
    rest
  ]>.
(*  match fA, gA with
  | <[[Tfi -> _]]>, <[[Tgi -> _]]> =>
    <[
      let rec h : <[[ fA * gA ]]> := (
        (
          fun _arg : Tfi ->
            let f := h.1 in
            let g := h.2 in
            ft _arg
        ),
        (
          fun _arg : Tgi ->
            let f := h.1 in
            let g := h.2 in
            gt _arg
        )
      ) in
      let f := h.1 in
      let g := h.2 in
      rest
    ]>
  | _, _ => <[ 1 1 ]>
  end.*)
(* [letrecand] grade 0/20 *)

Notation "'let' 'mut' f ':' Tf ':=' tf  'and' g ':' Tg ':=' tg 'in' z" :=
  (letrecand f Tf tf g Tg tg z)
    (in custom ML at level 90,
        f at level 99,
        Tf custom ML_ty at level 99,
        tf custom ML at level 99,
        g at level 99,
        Tg custom ML_ty at level 99,
        tg custom ML at level 99,
        z custom ML at level 99) : ML_scope.

(** Προκειμένου να ελέγξετε τις λύσεις σας, επεκτείνετε τον παρακάτω
    substitution-based interpreter με την αποτίμηση του τελεστή fix *)

Fixpoint eval (fuel : nat) (t : term) : option term :=
  match fuel with
  | 0 => fail
  | S fuel' =>
      match t with
      (* Application *)
      | <[ t1 t2 ]> =>
          v1 <- eval fuel' t1 ;;
          match v1 with
          | <[ fun x : T -> t' ]> =>
              v2 <- eval fuel' t2 ;;
              eval fuel' <[ [x := v2] t' ]>
          | _ => fail
          end
      (* Let *)
      | <[ let x := t1 in t2]> =>
          v <- eval fuel' t1 ;;
          eval fuel' <[ [x := v] t2 ]>
      (* If *)
      | <[ if t1 then t2 else t3 ]> =>
          v <-  eval fuel' t1 ;;
          match v with
          | T_Bool true => eval fuel' t2
          | T_Bool false => eval fuel' t3
          | _ => fail
          end
      (* Bop *)
      | T_BOp bop t1 t2 =>
          v1 <- eval fuel' t1 ;;
          v2 <- eval fuel' t2 ;;
          match v1, v2 with
          | T_Bool b1, T_Bool b2 =>
              match bop with
              | And => return (T_Bool (b1 && b2))
              | Or => return (T_Bool (b1 || b2))
              | _ => None
              end
          | T_Nat n1, T_Nat n2 =>
              match bop with
              | Plus => return (T_Nat (n1 + n2))
              | Minus => return (T_Nat (n1 - n2))
              | Mult => return (T_Nat (n1 * n2))
              | Lt => return (T_Bool (n1 <? n2))
              | Eq => return (T_Bool (n1 =? n2))
              | _ => fail
              end
          | _, _ => fail
          end
      (* Uop *)
      | T_UOp op t =>
          v <- eval fuel' t ;;
          match v with
          | T_Bool b =>
              match op with
              | Neg => return (T_Bool (negb b))
              end
          | _ => fail
          end
      (* Fst *)
      | T_Fst t =>
          v <- eval fuel' t ;;
          match v with
          | T_Pair v1 _ => return v1
          | _ => None
          end
      (* Snd *)
      | T_Snd t =>
          v <- eval fuel' t ;;
          match v with
          | T_Pair _ v2 => return v2
          | _ => None
          end
      (* Pair *)
      | T_Pair t1 t2 =>
          v1 <- eval fuel' t1 ;;
          v2 <- eval fuel' t2 ;;
          return <[ (v1, v2) ]>
      (* Left injection *)
      | <[ inl T t ]>  =>
          v <- eval fuel' t ;;
          return <[ inl T v ]>
      (* Right injection *)
      | <[ inr T t ]>  =>
          v <- eval fuel' t ;;
          return <[ inr T v ]>
      (* Case *)
      | <[ case t of | inl y1 => t1 | inr y2 => t2 ]> =>
          v <- eval fuel' t ;;
          match v with
          | <[ inl T v1 ]>  => eval fuel' <[ [y1 := v1] t1 ]> 
          | <[ inr T v2 ]> => eval fuel' <[ [y2 := v2] t2 ]>
          | _ => fail
          end
      (* Fix *)
      | <[ fix t ]> => 
        v <- eval fuel' t ;;
        match v with
        | <[ fun x : T -> t' ]> => eval fuel' <[ [x := fix t] t' ]>
        | _ => None
        end
      (* Values*)
      | <[ fun x : T -> t ]> => return  <[ fun x : T -> t ]>
      | T_Nat n => return (T_Nat n)
      | T_Bool b => return (T_Bool b)
      | T_Var x => None
      end
  end.

(* [eval] grade 0/20 *)

(** Tests *)

Definition fact : string := "fact".
Definition n : string := "n".
Definition even : string := "even".
Definition odd : string := "odd".

Definition myfact : term :=
  <[ let rec fact : Nat -> Nat :=
       fun n : Nat -> if n = 0 then 1 else n * fact (n - 1)
     in fact 5 ]>.

Definition even_odd : term :=
  <[
    let mut
      even : Nat -> Bool := fun n : Nat -> if n = 0 then true else odd (n-1)
    and
      odd : Nat -> Bool := fun n : Nat -> if n = 0 then false else even (n-1)
    in
      even 2
  ]>.

(** Εάν οι ορισμοί σας είναι σωστοί τα παρακάτω tests θα πρέπει να
    επιτυγχάνουν. *)

Example example1 : eval 5000 myfact = Some (T_Nat 120).
Proof. reflexivity. Qed.

Example example2 : eval 5000 even_odd = Some (T_Bool true).
Proof. reflexivity. Qed.

(** Bonus ερώτημα: ορίστε έναν environment-based interpreter, παρόμοιο
    με αυτόν της άσκησης 5, που να υποστηρίζει τον τελεστή [fix]. *)

Module EnvInterp.
  
  (** Environment-based Interpreter *)

  Definition var_map (A : Type) : Type := list (string * A).

  Definition empty {A} : var_map A := nil.

  Definition lookup {A} (var : string) (env : var_map A) : option A :=
    match find (fun '(x, _) => String.eqb x var) env with
    | Some (_, v) => Some v
    | None => None
    end.

  Definition add {A} (var : string) (val : A) (env : var_map A) : var_map A :=
    (var, val) :: env. 

  (** Hint: Eπεκτείνουμε τις τιμές του environment-based interpreter, με
      ένα closure για τα fixed-points το οποίο αναπαριστά ένα suspended
      unfolding του fixed point. *)
  
  Inductive value : Type :=
  (* Closure *)
  | V_Clo :
    var_map value ->
    string -> type -> term ->
    value
  | V_Fix : (* a suspended unfolding of the fix *)
    var_map value ->
    string -> type -> term ->
    value
  (* Natural Numbers *)
  | V_Nat : nat -> value
  (* Booleans *)
  | V_Bool : bool -> value
  (* Pairs *)
  | V_Pair : value -> value -> value
  (* Sums *)
  | V_Inl : value -> value
  | V_Inr : value -> value. 

  Definition environment : Type := var_map value.

  Fixpoint eval (fuel : nat) (env : environment) (t : term) : option value :=
    match fuel with
    | 0 => fail
    | S fuel' =>
        match t with
        (* Application *)
        | <[ t1 t2 ]> =>
            v1 <- eval fuel' t1 ;;
            match v1 with
            | <[ fun x : T -> t' ]> =>
                v2 <- eval fuel' t2 ;;
                eval fuel' <[ [x := v2] t' ]>
            | _ => fail
            end
        (* Let *)
        | <[ let x := t1 in t2]> =>
            v <- eval fuel' t1 ;;
            eval fuel' <[ [x := v] t2 ]>
        (* If *)
        | <[ if t1 then t2 else t3 ]> =>
            v <-  eval fuel' t1 ;;
            match v with
            | T_Bool true => eval fuel' t2
            | T_Bool false => eval fuel' t3
            | _ => fail
            end
        (* Bop *)
        | T_BOp bop t1 t2 =>
            v1 <- eval fuel' t1 ;;
            v2 <- eval fuel' t2 ;;
            match v1, v2 with
            | T_Bool b1, T_Bool b2 =>
                match bop with
                | And => return (T_Bool (b1 && b2))
                | Or => return (T_Bool (b1 || b2))
                | _ => None
                end
            | T_Nat n1, T_Nat n2 =>
                match bop with
                | Plus => return (T_Nat (n1 + n2))
                | Minus => return (T_Nat (n1 - n2))
                | Mult => return (T_Nat (n1 * n2))
                | Lt => return (T_Bool (n1 <? n2))
                | Eq => return (T_Bool (n1 =? n2))
                | _ => fail
                end
            | _, _ => fail
            end
        (* Uop *)
        | T_UOp op t =>
            v <- eval fuel' t ;;
            match v with
            | T_Bool b =>
                match op with
                | Neg => return (T_Bool (negb b))
                end
            | _ => fail
            end
        (* Fst *)
        | T_Fst t =>
            v <- eval fuel' t ;;
            match v with
            | T_Pair v1 _ => return v1
            | _ => None
            end
        (* Snd *)
        | T_Snd t =>
            v <- eval fuel' t ;;
            match v with
            | T_Pair _ v2 => return v2
            | _ => None
            end
        (* Pair *)
        | T_Pair t1 t2 =>
            v1 <- eval fuel' t1 ;;
            v2 <- eval fuel' t2 ;;
            return <[ (v1, v2) ]>
        (* Left injection *)
        | <[ inl T t ]>  =>
            v <- eval fuel' t ;;
            return <[ inl T v ]>
        (* Right injection *)
        | <[ inr T t ]>  =>
            v <- eval fuel' t ;;
            return <[ inr T v ]>
        (* Case *)
        | <[ case t of | inl y1 => t1 | inr y2 => t2 ]> =>
            v <- eval fuel' t ;;
            match v with
            | <[ inl T v1 ]>  => eval fuel' <[ [y1 := v1] t1 ]> 
            | <[ inr T v2 ]> => eval fuel' <[ [y2 := v2] t2 ]>
            | _ => fail
            end
        (* Fix *)
        | <[ fix t ]> => 
          v <- eval fuel' t ;;
          match v with
          | <[ fun x : T -> t' ]> => eval fuel' <[ [x := fix t] t' ]>
          | _ => None
          end
        (* Values*)
        | <[ fun x : T -> t ]> => return  <[ fun x : T -> t ]>
        | T_Nat n => return (T_Nat n)
        | T_Bool b => return (T_Bool b)
        | T_Var x => None
        end
    end.

  (* [eval_env] grade 0/20 *)

  (** Tests *)
  
  Definition eval_top (fuel : nat) (t : term) : option value :=
    eval fuel empty t. 

  Definition f : string := "f".
  Definition foo : string := "foo".
  Definition bar : string := "bar".

  Definition test1 : term := <[ let f := (fun x : Nat -> x + 4) in f 4 ]> .
  Definition test2 : term := <[ let foo := (fun x : Nat -> x + 7) in
                                let bar := (fun x : Nat -> x * 2) in
                                (foo (bar 4)) ]>.
  Definition test3 : term :=
    <[ let foo := fun n : Nat -> if n = 0 then 0 else n * n in foo 4]>.

  Definition test4 : term := <[ let foo :=
                                  (fun x : Nat ->
                                           let bar := fun y : Nat  -> x + y in bar) in
                                foo 7 8 ]>.

  
  (** Εάν ο ορισμός σας είναι σωστός τα παρακάτω tests θα πρέπει να
      επιτυγχάνουν. *)

  Example example1 : eval_top 1000 test1 = Some (V_Nat 8).
  Admitted. (* Για να ελέγξετε τον ορισμό σας, διαγράψτε αυτή τη γραμμή και κάντε uncomment την από κάτω. *)
  (* Proof. reflexivity. Qed. *)

  Example example2 : eval_top 1000 test2 = Some (V_Nat 15).
  Admitted. (* Για να ελέγξετε τον ορισμό σας, διαγράψτε αυτή τη γραμμή και κάντε uncomment την από κάτω. *)
  (* Proof. reflexivity. Qed. *)

  Example example3 : eval_top 1000 test3 = Some (V_Nat 16).
  Admitted. (* Για να ελέγξετε τον ορισμό σας, διαγράψτε αυτή τη γραμμή και κάντε uncomment την από κάτω. *)
  (* Proof. reflexivity. Qed. *)

  Example example4 : eval_top 1000 test4 = Some (V_Nat 15).
  Admitted. (* Για να ελέγξετε τον ορισμό σας, διαγράψτε αυτή τη γραμμή και κάντε uncomment την από κάτω. *)
  (* Proof. reflexivity. Qed. *)

  Example example5 : eval_top 1000 myfact = Some (V_Nat 120).
  Admitted. (* Για να ελέγξετε τον ορισμό σας, διαγράψτε αυτή τη γραμμή και κάντε uncomment την από κάτω. *)
  (* Proof. reflexivity. Qed. *)

  Example example6 : eval_top 1000 even_odd = Some (V_Bool true).
  Admitted. (* Για να ελέγξετε τον ορισμό σας, διαγράψτε αυτή τη γραμμή και κάντε uncomment την από κάτω. *)
  (* Proof. reflexivity. Qed. *)

End EnvInterp.
