Require Import Coq.Strings.String Coq.Arith.Arith Lia.
(* Suppress warnings when overriding notations *)
Set Warnings "-notation-overriden, -parsing".

Require Import imp.

(** Στοιχεία Σπουδαστή
Όνομα: ΔΗΜΗΤΡΙΟΣ ΓΕΩΡΓΟΥΣΗΣ
ΑΜ: 03119005
*)


(** * Εργασία 3 (100 μονάδες + 10 μονάδες bonus) *)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με
    την σημασιολογία απλών γλωσσών προγραμματισμού.

    Οδηγίες:

    - Εάν κολλήσετε σε κάποιο ενδιάμεσο lemma ή proof goal, μπορείτε
      να χρησιμοποιήσετε [admit] ώστε να ολοκληρώσετε την άσκηση και να
      βαθμολογηθείτε για ό,τι έχετε λύσει.

    - To παραδοτέο αρχείο θα πρέπει να κάνει compile. Τα αρχεία που
      δεν κάνουν compile δεν θα βαθμολογούνται.

    - Όταν ολοκληρώνετε κάποια απόδειξη, αντικαταστήστε το τελικό
      [Admitted] με [Qed].

    - Μην αλλάζετε τον κώδικα που σας έχει δωθεί. Μην γράφετε μέσα
      στα στα σχόλια της βαθμολόγησης. Αυτό είναι απαραίτητο για την
      ομαλή και έγκαιρη βαθμολόγηση των εργασιών. Μπορείτε να γράψετε
      όπου υπάρχει η οδηγία (* ___ FILL IN HERE ___ *). Εάν σας
      εξυπηρετεί, μπορείτε να ορίζετε βοηθητικές συναρτήσεις, λήμματα,
      ορισμούς, κ.α.

    - Μην αλλάζετε τα ονόματα των αρχείων. Γράψτε τις απαντήσεις σας
      μόνο σε αυτό το αρχείο.

    - Συμπληρώστε σωστά τα στοιχεία σας στην αρχή του αρχείου. Αυτό
      είναι απαραίτητο για την σωστή βαθμολόγηση των εργασιών. *)


(** ** Άσκηση 1: Προθέρμανση (15 μονάδες) *)


(** Γράψτε ένα πρόγραμμα Imp που να κάνει swap τις μεταβλητές [Χ] και [Y]. *)

(** Ονόματα μεταβλητών *)
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition RES : string := "RES".

Definition SWAP : com :=
  <{Z := X; X := Y; Y := Z}>.

(* [SWAP] grade 0/2 *)

(** Αποδείξτε την παρακάτω προδιαγραφή για το πρόγραμμα [SWAP]. *)

Lemma SWAP_correct :
  forall (st : imp_state),
  exists (st' : imp_state), st =[ SWAP ]=> st' /\ st' X = st Y /\ st' Y = st X.
Proof.
  intros st.
  eexists. repeat split.
  - unfold SWAP. repeat eapply E_Seq; apply E_Asgn; constructor.
  - unfold update_st. reflexivity.
  - unfold update_st. reflexivity.
Qed.

(* [SWAP_correct] grade 0/3 *)

(** Γράψτε ένα πρόγραμμα Imp που υπολογίζει το παραγοντικό ενός αριθμού [n]
    και αποθηκεύει την τιμή του στην μεταβλητή [RES] *)

Definition FACT (n : nat) : com :=
  <{
    X := 1;
    RES := 1;
    while X <= n do { RES := RES * X; X := X + 1 }
  }>.
(* [FACT] grade 0/3 *)

(** Αποδείξτε την παρακάτω προδιαγραφή για το πρόγραμμα [FACT]. *)

Lemma FACT_5_correct :
  forall (st : imp_state),
  exists (st' : imp_state), st =[ FACT 5 ]=> st' /\ st' RES = 120.
Proof.
  intros st.
  eexists. repeat split.
  {
    unfold FACT. repeat eapply E_Seq; try apply E_Asgn; try reflexivity.
    eapply E_WhileTrue; try reflexivity.
    {
      repeat eapply E_Seq; eapply E_Asgn; reflexivity.
    }
    simpl.
    eapply E_WhileTrue; try reflexivity.
    {
      repeat eapply E_Seq; eapply E_Asgn; reflexivity.
    }
    simpl.
    eapply E_WhileTrue; try reflexivity.
    {
      repeat eapply E_Seq; eapply E_Asgn; reflexivity.
    }
    simpl.
    eapply E_WhileTrue; try reflexivity.
    {
      repeat eapply E_Seq; eapply E_Asgn; reflexivity.
    }
    simpl.
    eapply E_WhileTrue; try reflexivity.
    {
      repeat eapply E_Seq; eapply E_Asgn; reflexivity.
    }
    simpl.
    eapply E_WhileFalse; reflexivity.
  }
  reflexivity.
Qed.

(* [FACT_correct] grade 0/7 *)


(** ** Άσκηση 2: Απλοποίηση αριθμητικών εκφράσεων (30 μονάδες) *)

(** Η άσκηση ζητάει να γραφτεί ένα πέρασμα βελτιστοποίησης για
    αριθμητικές εκφράσεις, το οποίο θα εφαρμόζει συγκεκριμένες
    αριθμητικές απλοποιήσεις. Οι απλοποιήσεις είναι οι εξής:

    e + 0 = e
    0 + e = e
    0 - e = 0
    e - 0 = e
    e * 1 = e
    1 * e = e
    e * 0 = 0
    0 * e = 0
*)

(** Γράψτε μια (μη αναδρομική) συνάρτηση [simplify] που
    ελέγχει αν ένας όρος έχει μια από τις παραπάνω μορφές και τον
    απλοποιεί.

    Για παράδειγμα ο όρος [<{ 0 + e }>] (δηλαδή το [APlus (ANum 0) e])
    θα πρέπει να απλοποιείται στο [e] *)

Definition simplify (e : aexp) : aexp :=
  match e with
  | APlus (ANum 0) e' => e'
  | APlus e' (ANum 0) => e'
  | AMinus e' (ANum 0) => e'
  | AMinus (ANum 0) _ => ANum 0
  | AMult (ANum 1) e' => e'
  | AMult e' (ANum 1) => e'
  | AMult (ANum 0) _ => ANum 0
  | AMult _ (ANum 0) => ANum 0
  | e' => e'
  end.

(* [simplify] grade 0/5 *)

(** Στη συνέχεια, γράψτε μια αναδρομική συνάρτηση [optimize] που να
    εφαρμόζει τη συνάρτηση simplify σε κάθε κόμβο του αφηρημένου
    συνακτικού δέντρου [aexp] με bottom-up τρόπο (δηλαδή από τους
    εσωτερικούς κόμβους προς τους εξωτερικούς). *)

Fixpoint optimize (e : aexp) : aexp :=
  match e with
  | APlus e1 e2 => simplify (APlus (optimize e1) (optimize e2))
  | AMinus e1 e2 => simplify (AMinus (optimize e1) (optimize e2))
  | AMult e1 e2 => simplify (AMult (optimize e1) (optimize e2))
  | e' => simplify e'
  end.

(* [optimize] grade 0/3 *)

(** Sanity check: Εάν οι παραπάνω ορισμοί είναι σωστοί, τοτε τα παρακάτω tests θα πρέπει να επιτυγχάνουν. *)

Example test_optimize1: (optimize <{ 3 + (X * 1) - 1 * 4 * (1 * Y - 0) }> = <{ 3 + X - 4 * Y }>).
Proof. reflexivity. Qed.

Example test_optimize2: (optimize <{ 3 + (X * 1) - Z * (0 * Y + (0 + 0)) }> = <{ 3 + X }>).
Proof. reflexivity. Qed.

Example test_optimize3: (optimize <{ (0 + (0 * X + 0)) - Z }> = <{ 0 }>).
Proof. reflexivity. Qed.


(** Αποδείξτε ότι οι παραπάνω συναρτήσεις είναι σωστές, δηλαδή
    διατηρούν τη σημασιολογία της αρχικής έκφρασης. *)

(** Ξεκινήστε αποδεικνύοντας ότι [ainterp st (simplify e) = ainterp st e].

    Σημείωση 1: Εφόσον ο ορισμός της παραπάνω συνάρτησης δεν είναι
    αναδρομικός, δεν θα χρειαστεί να κάνετε απόδειξη με επαγωγή.

    Σημείωση 2: Η παρακάτω απόδειξη έχει (πάρα) πολλές παρόμοιες
    περιπτώσεις.  Μπορείτε να χρησιμοποιήσετε τις τεχνικές που μάθαμε
    στο μάθημα ώστε να ομαδοποιήσετε διαφορετικές περιπτώσεις της
    απόδειξης.

    Προκειμένου αυτό να γίνει πιο εύκολο, σας δίνεται το tactic
    [simpl_arith] το οποιο εφαρμόζει τους παραπάνω κανόνες απλοποίησης
    στους φυσικούς αριθμούς. To tactic αυτό ομαδοποιεί διάφορες
    απλοποιήσεις που θα χρειαστεί να κάνετε στο αποτέλεσμα του
    interpreter σε διάφορες περιπτώσεις της απόδειξής σας. Θα σας
    φανεί χρήσιμο ώστε να γράψετε proof scripts που  μπορούν να
    εφαρμοστούν σε πολλές παρόμοιες περιπτώσεις της απόδειξης.  *)

Ltac simpl_arith :=
  try rewrite <- plus_n_O; try rewrite plus_O_n;
  try rewrite PeanoNat.Nat.mul_1_r; try rewrite PeanoNat.Nat.mul_1_l;
  try rewrite PeanoNat.Nat.mul_0_r; try rewrite PeanoNat.Nat.mul_0_l;
  try rewrite PeanoNat.Nat.sub_0_l; try rewrite PeanoNat.Nat.sub_0_r.

Lemma simplify_correct :
  forall (st : imp_state) (e : aexp), ainterp st (simplify e) = ainterp st e.
Proof.
  intros st e.
  destruct e.
  - reflexivity.
  - reflexivity.
  - simpl.
    destruct e1 as [n1 | s1 | e1 | e1 | e1]; try destruct n1;
    destruct e2 as [n2 | s2 | e2 | e2 | e2]; try destruct n2;
    simpl_arith; reflexivity.
  - simpl.
    destruct e1 as [n1 | s1 | e1 | e1 | e1]; try destruct n1;
    destruct e2 as [n2 | s2 | e2 | e2 | e2]; try destruct n2;
    simpl_arith; reflexivity.
  - simpl.
    destruct e1 as [n1 | s1 | e1 | e1 | e1]; try destruct n1 as [ | n1]; try destruct n1 as [ | n1];
    destruct e2 as [n2 | s2 | e2 | e2 | e2]; try destruct n2 as [ | n2]; try destruct n2 as [ | n2];
    simpl_arith; reflexivity.
Qed.

 (* [simplify_correct] grade 0/10 *)

(**  Στη συνέχεια, χρησιμοποιώντας το παραπάνω λήμμα, αποδείξτε ότι
     [ainterp st (optimize e) = ainterp st e]. *)

(** Η εντολή [Opaque simplify] θα αποτρέψει το [simplify] από το να
    γίνει expand στον ορισμό όταν κάνετε [simpl]. Αυτό είναι χρήσιμο
    ώστε να μην αντικατασταθούν οι κλήσεις στην [simplify] με το σώμα
    της συνάρτησης και να μπορέσετε να εφαρμόσετε το παραπάνω
    λήμμα. *)

Opaque simplify.

Lemma optimize_correct :
  forall (st : imp_state) (e : aexp), ainterp st (optimize e) = ainterp st e.
Proof.
  intros st e. induction e.
  - unfold optimize. apply simplify_correct.
  - unfold optimize. apply simplify_correct.
  - simpl.
    rewrite simplify_correct with (e := <{ (optimize e1) + (optimize e2) }>).
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - simpl.
    rewrite simplify_correct with (e := <{ (optimize e1) - (optimize e2) }>).
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - simpl.
    rewrite simplify_correct with (e := <{ (optimize e1) * (optimize e2) }>).
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

 (* [optimize_correct] grade 0/7 *)

Transparent simplify.

 (** Τέλος, γράψτε μια αναδρομική συνάρτηση [optimize_com] που
     εφαρμόζει αυτή την βελτιστοποίηση σε _όλες_ τις αριθμητικές
     εκφράσεις που εμφανίζονται σε ένα αφηρημένο συντακτικό δέντρο
     [com]. Διατυπώστε και αποδείξτε ένα θεώρημα για την ορθότητα
     αυτoύ του μετασχηματισμού. Χρησιμοποιήστε τον ορισμό [ceval] της
     big-step σημασιολογίας.  *)

Fixpoint optimize_com (c : com) : com :=
  match c with
  | CSkip => CSkip
  | CAsgn name val => CAsgn name (optimize val)
  | CSeq hd tl => CSeq (optimize_com hd) (optimize_com tl)
  | CIf b c1 c2 => CIf b (optimize_com c1) (optimize_com c2)
  | CWhile b c => CWhile b (optimize_com c)
  end.

(* [optimize_com] grade 0/3 *)

(** Sanity check: Εάν ο παραπάνω ορισμος είναι σωστός, τοτε το παρακάτω test θα πρέπει να επιτυγχάνει. *)

Example test_optimize_com:
  optimize_com <{ Z := Y + (1 * (X + 1))*0; while (Z <> 0) do { Z := Z * 1 - 1; X := X - 0 + 1 } }> =
  <{ Z := Y; while (Z <> 0) do { Z := Z - 1; X := X + 1 } }>.
Proof. simpl. reflexivity. Qed.

Theorem optimize_com_correct :
  forall (st : imp_state) (c : com) (st' : imp_state),
  st =[ c ]=> st' -> st =[ optimize_com c ]=> st'.
Proof.
  intros st c st' H.
  induction c.
  - simpl. assumption.
  - simpl.


(* [optimize_com_correct] grade 0/7 *)



(** ** Άσκηση 3: For Loops (50 μονάδες) *)

(** Σε αυτή την άσκηση σας ζητείται να προσθέσετε for loops στην γλώσσα
    Imp.

    Ένα for loop επεκτείνει την γραμματική των εντολών <com> ως εξής:

    <com> := ... | for <com>; <bexp>; <com> do <com>

    Η πρώτη παράμετρος <com> εκτελείται μια φορά στην αρχή της
    εκτέλεσης του loop.

    Η δεύτερη παράμετρος <bexp> είναι η συνθήκη που καθορίζει αν η
    εκτέλεση του loop θα συνεχιστεί.

    Η τρίτη παράμετρος <com> εκτελείται μετά το τέλος κάθε επανάληψης
    του σώματος του loop.

    Τέλος, η τέταρτη παράμετρος <com> είναι το σώμα του loop.

    Για παράδειγμα το παρακάτω πρόγραμμα προσθέτει 5 στην τιμή της
    μεταβλητής [Υ].

    <{ for Z = 0; Z < 5; Z := Z + 1 do Y := Y + 1 }> *)

Module ForLoops.

  (** Eπεκτείνετε τον ορισμό του [com] με έναν κόμβο [CFor] που
      αναπαριστά το for loop *)
  Inductive com : Set :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (** __ FILL IN HERE __ **)
  .

  (* [com] grade 0/3 *)

  (** Επαναορίζουμε τα σχετικά notations ώστε να αναφέρονται στον νέο
      ορισμό [com]. *)

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


 (** Αφού επεκτείνετε τον ορισμό του [com], κάντε uncomment τον
     σωστό ορισμό του παρακάτω notation. Η χρήση του στον κώδικα
     σας είναι προαιρετική. Μπορείτε να χρησιμοποιείτε κατευθείαν
     τους constructors του [com]. *)

 Notation "'for' i ';' b ';' f 'do' c" :=
 (* Προσοχή!!! Αυτός ο ορισμός είναι λάθος.  *)
   (CIf b (CSeq i f) c)
     (in custom com at level 88, b at level 89,
         i at level 89, f at level 89, c at level 89) : com_scope.
 (* Aφού συμπληρώσετε τους παραπάνω ορισμούς, διαγράψτε τον παραπάνω
    ορισμό του notation και κάντε uncomment τον παρακάτω κώδικα.*)
 (*   (CFor i b f c) *)
 (*     (in custom com at level 88, b at level 89, *)
 (*         i at level 89, f at level 89, c at level 89) : com_scope. *)


 Reserved Notation "st '=[' c ']=>' st'"
   (at level 40, c custom com at level 99, st constr, st' constr at next level).

 (** Επεκτείνετε τον ορισμό [ceval] των big-step semantics με τις
     απαραίτητες περιπτώσεις για την εκτέλεση του for. Ίσως βρείτε
     βοηθητικό να γράψετε πρώτα στο χαρτί τα derivation rules για τo
     for loop και μετά να τα μετατρέψετε σε κώδικα. *)

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
  (** __ FILL IN HERE __ **)
  where "st =[ c ]=> st'" := (ceval st c st').

  (* [ceval] grade 0/10 *)

  (** Κάντε uncomment το παρακάτω πρόγραμμα. *)
  Definition addX5 : com (* := <{ for Z := 0; Z < 5 ; Z := Z + 1 do Y := Y + 1 }>.  *)
  . Admitted. (* Διαγράψτε αυτή τη γραμμή και κάντε uncomment την από πάνω. *)


  (** Αποδείξτε την παρακάτω προδιαγραφή για το πρόγραμμα [addX5]. Σας
      δίνεται το tactic [simplify_state] που απλοποιεί τα states που
      προκύπτουν απο το παραπάνω πρόγραμμα.

      Συγκεκριμένα κάνει τις εξής απλοποιήσεις, για κάθε τιμή [st] και [v].

       (Ζ !-> v; st) Y = st y
       (Y !-> v; st) Y = v

      Μπορείτε να το χρησιμοποιήσετε να απλοποιήσετε τα ενδιάμεσα
      και το τελικό states. Για να το εφαρμόσετε πολλές φορές
      χρησιμοποιήστε το μαζί με το tactical [repeat]. *)


  Ltac simplify_state :=
    match goal with
    | |- context[update_st ?st1 Z ?v Y] =>
        replace (update_st st1 Z v Y) with (st1 Y) by reflexivity
    | |- context[update_st ?st1 Y ?v Y] =>
        replace (update_st st1 Y v Y) with v by reflexivity
    end.

  Lemma addX5_correct :
    forall (st : imp_state),
    exists (st' : imp_state), st =[ addX5 ]=> st' /\ st' Y = st Y + 5.
  Proof.
    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [addX5_correct] grade 0/12 *)

  (** Επεκτείνετε την απόδειξη ότι το [ceval] είναι μια ντερεμινιστική σχέση. *)
  Lemma ceval_deterministic :
  forall st c st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
  Proof.
    intros st c st1 st2 Heval1. revert st2.
    induction Heval1; intros st2 Heval2.
    - (* E_Skip *)
      inv Heval2. reflexivity.
    - (* E_Asgn *)
      inv Heval2. reflexivity.
    - (* E_Seq *)
      inv Heval2. apply IHHeval1_2.

      rewrite IHHeval1_1 with (st2 := st'0).
      + assumption.
      + assumption.

    - (* E_IfTrue *)
      inv Heval2. (* can be either [E_IfTrue] or [E_IfFalse] *)
      + apply IHHeval1. assumption.
      + congruence. (* contradiction *)

    - (* E_IfFalse *)
      inv Heval2. (* can be either [E_IfTrue] or [E_IfFalse] *)
      + congruence. (* contradiction *)
      + apply IHHeval1. assumption.

    - (* E_WhileFalse *)
      inv Heval2. (* can be either [E_WhileFalse] or [E_WhileTrue] *)
      + reflexivity.
      + congruence. (* contradiction *)

    - (* E_WhileTrue *)
      inv Heval2. (* can be either [E_WhileFalse] or [E_WhileTrue] *)
      + congruence. (* contradiction *)
      + apply IHHeval1_2.

        rewrite IHHeval1_1 with (st2 := st'0).
        * assumption.
        * assumption.

    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [ceval_deterministic] grade 0/25 *)

  (** *Bonus* ερωτήματα: αποδείξτε ότι το [for] μπορεί να γραφεί ισοδύναμα ως while. *)

  (** Αποδείξτε πρώτα ότι αν ξεκινώντας από ένα state το for
      τερματιζει σε ένα τελικό state, τότε η εκτέλεση του while στο
      ίδιο αρχικό state τερματίζει στο ίδιο τελικό state *)

  Lemma for_while :
    forall (st st' : imp_state) (i : com) (b : bexp) (f c : com),
      st =[ for i ; b ; f do c ]=> st' ->
      st =[ i; while b do { c ; f } ]=> st'.
  Proof.
    intros st st' i b f c Heval.
    (* προκειμένου να κάνουμε επαγωγή στο derivation Ηeval πρέπει όλα
       τα ορίσματα του να είναι μεταβλητές. Για το λόγο αυτό
       θέτουμε μια καινούρια μεταβλητή [c'] με την τιμή [for i ; b ; f do c ]
       και την αντικαθιστούμε στον τύπο του [Heval]. *)

    remember (<{ for i; b; f do c }>) as c' eqn:Heq.

    (* γενικεύουμε όλες τις μεταβλητές που δεν εμφανίζονται στο [Heval] *)
    revert i b c f Heq.

    (* κάνουμε επαγωγή στο derivation [Heval] *)
    induction Heval.

    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [for_while] grade 0/5 *)


  (** Για να δείξετε την άλλη κατεύθυνση, αποδείξτε πρώτα ένα ότι ένα
      while ισοδυναμεί με ένα for χωρίς εντολή αρχικοποίησης. *)

  Lemma while_for_aux :
    forall (st st' : imp_state) (i : com) (b : bexp) (f c : com),
      st =[ while b do { c ; f } ]=> st' ->
      st =[ for skip ; b ; f do c ]=> st'.
  Proof.
    intros st st' i b f c Heval.
    (* για την επαγωγή ακολουθούμε την ίδια τεχνική με το παραπάνω λήμμα *)
    remember (<{ while b do { c ; f } }> ) as c' eqn:Heq.
    revert b c f Heq.
    induction Heval.
    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [while_for_aux] grade 0/4 *)


  (** Χρησιμοποιώντας το παραπάνω λήμμα, μπορούμε να δείξουμε το τελικό λήμμα. *)

  Lemma while_for :
    forall (st st' : imp_state) (i : com) (b : bexp) (f c : com),
      st =[ i; while b do { c ; f } ]=> st' ->
      st =[ for i ; b ; f do c ]=> st'.
  Proof.
    (*  ___ FILL IN HERE ___ *)
  Admitted.

  (* [while_for] grade 0/1 *)

End ForLoops.
