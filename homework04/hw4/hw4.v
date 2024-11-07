Require Import Coq.Strings.String Coq.Arith.Arith Coq.Init.Nat Lia.
Require Import imp hoare.

(* Suppress warnings when overriding notations *)
Set Warnings "-notation-overriden, -parsing".

(** Στοιχεία Σπουδαστή
Όνομα: ΔΗΜΗΤΡΙΟΣ ΓΕΩΡΓΟΥΣΗΣ
ΑΜ: 03119005
*)


(** * Εργασία 4 (100 μονάδες + 30 μονάδες bonus) *)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με την
    επαλήθευση προγραμμάτων χρησιμοποιώντας τη λογική Hoare.

    Οδηγίες:

    - Μπορείτε να διαλέξετε μεταξύ 2 από τις 3 ασκήσεις. Η επιλογή και
      των τριών δίνει 30 μονάδες bonus.

    - Εάν κολλήσετε σε κάποιο ενδιάμεσο lemma ή proof goal, μπορείτε
      να χρησιμοποιήσετε [admit] ώστε να ολοκληρώσετε την άσκηση και
      να βαθμολογηθείτε για ό,τι έχετε λύσει.

    - Το παραδοτέο αρχείο θα πρέπει να κάνει compile. Τα αρχεία που
      δεν κάνουν compile δεν θα βαθμολογούνται.

    - Όταν ολοκληρώνετε κάποια απόδειξη, αντικαταστήστε το τελικό
      [Admitted] με [Qed].

    - Μην αλλάζετε τον κώδικα που σας έχει δοθεί. Μην γράφετε μέσα στα
      σχόλια της βαθμολόγησης. Αυτό είναι απαραίτητο για την ομαλή και
      έγκαιρη βαθμολόγηση των εργασιών. Μπορείτε να γράψετε όπου
      υπάρχει η οδηγία (* ___ FILL IN HERE ___ *). Εάν σας εξυπηρετεί,
      μπορείτε να ορίζετε βοηθητικές συναρτήσεις, λήμματα, ορισμούς,
      κ.α.

    - Μην αλλάζετε τα ονόματα των αρχείων. Γράψτε τις απαντήσεις σας
      μόνο σε αυτό το αρχείο και στο αρχείο fastpow.dfy αν επιλέξετε
      να κάνετε την άσκηση 3.

    - Συμπληρώστε σωστά τα στοιχεία σας στην αρχή του αρχείου. Αυτό
      είναι απαραίτητο για τη σωστή βαθμολόγηση των εργασιών. *)


(** ** Άσκηση 1: Επαναλαμβανόμενος τετραγωνισμός στην Imp (50 μονάδες) *)

(** Η άσκηση σας ζητά να γράψετε ένα πρόγραμμα στη γλώσσα Imp που θα
    υπολογίζει την ύψωση σε δύναμη χρησιμοποιώντας τη μέθοδο του
    επαναλαμβανόμενου τετραγωνισμού (exponentiation by squaring). Η
    βάση και ο εκθέτης δίνονται ως ορίσματα. Στη συνέχεια, η άσκηση
    σας ζητά να αποδείξετε την ορθότητα του προγράμματος
    χρησιμοποιώντας τη λογική Hoare.

    Μπορείτε να ακολουθήσετε μία από τις παρακάτω μεθόδους:

    - Να γράψετε το πρόγραμμα σε απλή Imp και να αποδείξετε το
      πρόγραμμα σωστό χρησιμοποιώντας τους κανόνες της λογικής Hoare.

    - Να γράψετε το πρόγραμμα σε annotated Imp, όπου το while loop θα
      πρέπει να είναι annotated με ένα κατάλληλο assertion, και να το
      αποδείξετε σωστό χρησιμοποιώντας weakest preconditions και
      verification conditions μέσω του λήμματος [verify_triple].

    Σημείωση: Οι τύποι και οι διατυπώσεις που έχουν δοθεί αντιστοιχούν
    στην δεύτερη μεθοδολογία. Εάν επιλέξετε την πρώτη θα πρέπει να τους
    προσαρμόσετε κατάλληλα.

    Σε κάθε περίπτωση θα πρέπει να βρείτε ένα κατάλληλο loop
    invariant. Θα σας βοηθήσει να σκεφτείτε μια έκφραση που
    περιλαμβάνει τις μεταβλητές που μεταβάλλονται κατά τη διάρκεια του
    loop, της οποίας όμως η τιμή παραμένει σταθερή κατά την είσοδο στο
    loop και μετά από κάθε επανάληψη.

    Σημείωση: Για τη διευκόληνση των ορισμών, οι αριθμητικές εκφράσεις
    στο συνοδευτικό αρχείο imp.v έχουν επεκταθεί με τις πράξεις της
    ακαίρεας διαίρεσης (div) και του υπόλοιπου της ακαίρεας διαίρεσης
    (mod). Μπορείτε να δείτε τη σημασιολογία τους αλλά και τα
    notations τους στο αρχείο imp.v. *)


Definition BASE := "base".
Definition EXP := "exp".

Definition FAST_EXP_INV (base exp : nat) : assertion :=
  fun st => st RES * st BASE ^ st EXP = base ^ exp.

Definition FAST_EXP (base exp : nat) : acom :=
  <[
    BASE := base;
    EXP := exp;
    RES := 1;

    while 0 < EXP {{ FAST_EXP_INV base exp }} do {
      if EXP % 2 = 1
      then RES := RES * BASE
      else skip;

      EXP := EXP / 2;
      BASE := BASE * BASE
    }
  ]>.

(* [FAST_EXP] grade 0/10 *)

Definition INV (base exp : nat) : assertion := FAST_EXP_INV base exp.

(* [INV] grade 0/10 *)


(** Sanity check: Εάν οι παραπάνω ορισμοί είναι σωστοί, τότε τα
    παρακάτω tests θα πρέπει να επιτυγχάνουν. *)

Example FAST_EXP_2_6 :
  match cinterp 20 (_ !-> 0) (erase (FAST_EXP 2 6)) with
  | Some st => Some (st RES) (* Get the value of variable [RES] in the state *)
  | None => None
  end = Some 64.
Proof. reflexivity. Qed.

Example FAST_EXP_3_4 :
  match cinterp 20 (_ !-> 0) (erase (FAST_EXP 3 4)) with
  | Some st => Some (st RES) (* Get the value of variable [RES] in the state *)
  | None => None
  end = Some 81.
Proof. reflexivity. Qed.

(** Η παρακάτω εντολή θα αποτρέψει τους ορισμούς του [modulo] και του [div]
    να γίνουν simplify κατά τη διάρκεια της απόδειξης σας. *)
Opaque modulo div.

(** Αποδείξτε ότι μετά την εκτέλεση του προγράμματος [FAST_EXP], η
    μεταβλητή [RES] θα έχει την τιμή [pow base exp], όπου [pow] είναι
    η συνάρτηση ύψωσης σε δύναμη από τo standard library. Μπορείτε να
    χρησιμοποιήσετε οποιοδήποτε λήμμα από τη βιβλιοθήκη χρειάζεται για
    την απόδειξη, όπως τα [Nat.pow_mul_l] και [Nat.pow_add_r], τα
    οποία μπορεί να φανούν χρήσιμα.

    Tips:

    - Χρησιμοποιήστε την εντολή [Search] για να βρείτε διαθέσιμα
      λήμματα που σχετίζονται με αριθμητικές ιδιότητες. Για
      παράδειγμα, η εντολή [Search (_ mod _).] εμφανίζει όλα τα
      λήμματα που αφορούν τον τελεστή [mod] του standard library.

    - Μπορείτε να χρησιμοποιήσετε τα tactics [unfold_all] και
      [simplify_env] που ορίσαμε στο μάθημα για να απλοποιήσετε
      το proof state.

    - Ίσως σας φανεί χρήσιμο να αποδείξετε τη διατήρηση του loop
      invariant και την επάρκειά του (ότι δηλαδή συνεπάγεται το
      επιθυμητό postcondition) "στο χαρτί" πριν προχωρήσετε στην
      απόδειξη σε Coq. *)

Corollary divmod2 : forall e, e = 2 * (e / 2) + e mod 2.
Proof.
  intros. apply Nat.div_mod; lia.
Qed.

Corollary n_plus_n : forall n, n + n = 2 * n.
Proof.
  intros. lia.
Qed.

Corollary n_square_m : forall n m, (n * n) ^ m = n ^ (2 * m).
Proof.
  intros. simpl. rewrite Nat.add_0_r.
  assert (n * n = n ^ 2). simpl. lia.
  rewrite H.
  rewrite <- Nat.pow_mul_r.
  simpl. rewrite Nat.add_0_r. reflexivity.
Qed.

Theorem FAST_EXP_CORRECT (base exp : nat) :
  {{ fun _ => True }} erase (FAST_EXP base exp) {{ fun st => st RES = pow base exp }}.
Proof.
  apply verify_triple.
  {
    repeat split.
    - intros Hmod.
      destruct H as [Hinv Hcond].
      unfold assertion_sub. simpl.
      unfold FAST_EXP_INV in *.
      unfold_all. simpl in *.
      apply Nat.eqb_eq in Hmod.
      apply Nat.ltb_lt in Hcond.
      remember (divmod2 (st EXP)) as Hexp. clear HeqHexp.
      rewrite Hmod in Hexp.
      rewrite Hexp in Hinv.
      rewrite Nat.add_comm in Hinv. simpl in Hinv. rewrite Nat.add_0_r in Hinv.
      rewrite n_plus_n with (n := st EXP / 2) in Hinv.
      rewrite <- n_square_m with (n := st BASE) in Hinv.
      rewrite Nat.mul_assoc in Hinv.
      assumption.
    - intros Hmod.
      destruct H as [Hinv Hcond].
      unfold assertion_sub. simpl.
      unfold FAST_EXP_INV in *.
      unfold_all. simpl in *.
      apply Nat.eqb_neq in Hmod.
      apply Nat.ltb_lt in Hcond.
      assert (Hmode : forall e, e mod 2 <> 1 <-> e mod 2 = 0). {
        intros. split; intros.
        - assert (e mod 2 < 2). apply Nat.mod_upper_bound. lia.
          lia.
        - lia.  
      }
      rewrite Hmode in Hmod. clear Hmode.
      remember (divmod2 (st EXP)) as Hexp. clear HeqHexp.
      rewrite Hmod in Hexp.
      rewrite Nat.add_0_r in Hexp.
      rewrite Hexp in Hinv.
      rewrite <- n_square_m with (n := st BASE) in Hinv.
      assumption.
    - intros st Hinv.
      destruct Hinv as [Hinv Hcond].
      unfold FAST_EXP_INV in *.
      unfold_all. simpl in *.
      apply Nat.ltb_ge in Hcond.
      assert (Hcexp : st EXP = 0). lia. clear Hcond.
      rewrite Hcexp in Hinv.
      rewrite Nat.pow_0_r in Hinv.
      rewrite <- Hinv.
      lia.
  }
  {
    intros st _.
    simpl. unfold assertion_sub. simpl.
    unfold FAST_EXP_INV. simpl.
    unfold update_st. simpl.
    lia.
  }
Qed.


(* [FAST_EXP_CORRECT] grade 0/30 *)


(** ** Άσκηση 2: Require and Assert (50 μονάδες) *)

(** Σε αυτή την άσκηση, επεκτείνουμε τη γλώσσα IMP με δύο εντολές,
    [require] και [assert]. Και οι δύο εντολές πραγματοποιούν έναν
    δυναμικό έλεγχο μίας boolean συνθήκης κατά τη διάρκεια εκτέλεσης
    ενός προγράμματος.

    Η σημασιολογία των δύο εντολών είναι η εξής:

    - Εάν η boolean συνθήκη του [assert] αποτιμηθεί σε [false], το
      πρόγραμμα τερματίζει σε μια κατάσταση σφάλματος. Εάν αποτιμηθεί
      σε [true], το πρόγραμμα συνεχίζει κανονικά την εκτέλεσή του.

    - Εάν μια δήλωση [require] αποτύχει, το πρόγραμμα αδυνατεί να
      αποτιμηθεί και "κολλάει". Η αποτίμηση του προγράμματος δεν
      παράγει κάποια τελική κατάσταση. Εάν η boolean συνθήκη
      αποτιμηθεί σε [true], το πρόγραμμα συνεχίζει κανονικά την
      εκτέλεσή του.

    Hint: οι αποδείξεις σε αυτή την άσκηση είναι αρκετά απλές και δεν
    χρειάζονται επαγωγή.
 *)

Module RequireAssert.

  Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRequire : bexp -> com (* νέα εντολή! *)
  | CAssert : bexp -> com  (* νέα εντολή! *)
  .

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

  (* νέο notation! *)
  Notation "'assert' l" := (CAssert l)
                             (in custom com at level 8, l custom com at level 0).

  (* νέο notation! *)
  Notation "'require' l" := (CRequire l)
                             (in custom com at level 8, l custom com at level 0).

  (** Πλέον, η εκτέλεση του προγράμματος δεν παράγει απλώς μια τελική
      κατάσταση [imp_state], αλλά ένα αποτέλεσμα που μπορεί να είναι
      είτε μια επιτυχής τελική κατάσταση είτε μια κατάσταση
      σφάλματος. *)

  Inductive result : Type :=
  | Success : imp_state -> result
  | Error   : result.

  Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

  (** Μελετήστε τους νέους κανόνες των big-step semantics της γλώσσας
      Imp. Στη συνέχεια επεκτείνετε τη σημασιολογία ώστε να
      περιλαμβάνει κανόνες για το [assert] και το [require]. *)

  Inductive ceval : imp_state -> com -> result -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> Success st
  | E_Asgn : forall st a n x,
      ainterp st a = n ->
      st =[ x := a ]=> Success (x !-> n ; st)
  | E_Seq_Success : forall c1 c2 st st' res,
      st =[ c1 ]=> Success st' ->
      st' =[ c2 ]=> res ->
      st =[ c1 ; c2 ]=> res
  | E_Seq_Error : forall c1 c2 st,
      st =[ c1 ]=> Error ->
      st =[ c1 ; c2 ]=> Error
  | E_IfTrue : forall st res b c1 c2,
      binterp st b = true ->
      st =[ c1 ]=> res ->
      st =[ if b then c1 else c2]=> res
  | E_IfFalse : forall st res b c1 c2,
      binterp st b = false ->
      st =[ c2 ]=> res ->
      st =[ if b then c1 else c2 ]=> res
  | E_WhileFalse : forall b st c,
      binterp st b = false ->
      st =[ while b do c ]=> Success st
  | E_WhileTrue_Success : forall st st' res b c,
      binterp st b = true ->
      st =[ c ]=> Success st' ->
      st' =[ while b do c ]=> res ->
      st =[ while b do c ]=> res
  | E_WhileTrue_Error : forall st b c,
      binterp st b = true ->
      st =[ c ]=> Error ->
      st =[ while b do c ]=> Error
  | E_AssertTrue : forall st b,
      binterp st b = true ->
      st =[ assert b ]=> Success st
  | E_AssertFalse : forall st b,
      binterp st b = false ->
      st =[ assert b ]=> Error
  | E_Require : forall st b,
      binterp st b = true ->
      st =[ require b ]=> Success st
  (** Δεν υπάρχει κανόνας για το: | E_RequireFalse : ... *)

  where "st =[ c ]=> st'" := (ceval st c st').

  (* [ceval] grade 0/10 *)


  (** Εάν ο ορισμός της σημασιολογίας είναι σωστός, θα πρέπει να
      μπορείτε να αποδείξετε τα παρακάτω λήμματα. *)

  Example eval_require_false :
    forall st, ~ exists st', st =[ X := 42; require (X < 11) ]=> st'.
  Proof.
    intros st H.
    destruct H as [st' H].
    inv H.
    - inv H3.
      inv H5. unfold update_st in H1. simpl in H1. rewrite Nat.ltb_lt in H1. lia.
    - inv H4.
  Qed.

  (* [eval_require_false] grade 0/3 *)

  Example eval_assert_false :
    forall st, st =[ X := 42; assert (X < 11) ]=> Error.
  Proof.
    intros st.
    eapply E_Seq_Success.
    - apply E_Asgn. simpl. reflexivity.
    - apply E_AssertFalse. reflexivity.
  Qed.

  (* [eval_assert_false] grade 0/3 *)

  Lemma require_true :
    forall c st res, st =[ c ]=> res -> st =[ require true; c ]=> res.
  Proof.
    intros.
    eapply E_Seq_Success.
    - apply E_Require. reflexivity.
    - assumption.
  Qed.

  (* [require_true] grade 0/3 *)

  Lemma assert_true :
    forall c st st', st =[ c ]=> Success st' -> st =[ c; assert true ]=> Success st'.
  Proof.
    intros.
    eapply E_Seq_Success.
    - apply H.
    - apply E_AssertTrue. reflexivity.
  Qed.

  (* [assert_true] grade 0/3 *)


  (** Στη συνέχεια ορίζουμε κανόνες λογικής Hoare για την επέκταση της
      Imp.  Η σημασιολογία μιας τρίπλας [{{ P }} c {{ Q }}] είναι η
      εξής:

      Εάν το πρόγραμμα [c] ξεκινάει από μια αρχική κατάσταση που
      ικανοποιεί το [P] και τερματίζει σε ένα αποτέλεσμα, τότε το
      αποτέλεσμα είναι μια επιτυχής τελική κατάσταση που ικανοποιεί το
      [Q].

      Παρατηρήστε ότι μια προδιαγραφή Hoare πλέον εγγυάται ότι το
      πρόγραμμα τερματίζει σε μια επιτυχή κατάσταση

      Οι κανόνες για τις ήδη υπάρχουσες εντολές παραμένουν οι ίδιοι.
      Προσθέστε δύο καινούριους κανόνες: έναν για την εντολή [require]
      και έναν για την εντολή [assert]. *)

  Reserved Notation "{{ P }} c {{ Q }}"
    (at level 90, c custom com at level 99).

  Inductive triple : assertion -> com -> assertion -> Type :=
  | H_Skip :
    forall (P : assertion),
      {{ P }} <{ skip }> {{ P }}
  | H_Asgn :
    forall (Q : assertion) (X : string) (a : aexp),
      {{ Q [X |-> a] }} <{ X := a }> {{ Q }}
  | H_Seq :
    forall (P Q R : assertion) (c1 c2 : com),
     {{ Q }} c2 {{ R }} ->
     {{ P }} c1 {{ Q }} ->
     {{ P }} <{ c1 ; c2 }> {{ R }}
  | H_If :
    forall (P Q : assertion) (b : bexp) (c1 c2 : com),
     {{ P AND (TRUE b) }} c1 {{ Q }} ->
     {{ P AND (FALSE b) }} c2 {{ Q }} ->
     {{ P }} <{if b then c1 else c2 }> {{ Q }}
  | H_While :
    forall (P : assertion) (b : bexp) (c : com),
      {{ P AND (TRUE b) }} c {{ P }} ->
      {{ P }} <{ while b do c }> {{ P AND (FALSE b) }}
  | H_PostWeakening :
    forall (P Q Q' : assertion) (c : com),
      {{ P }} c {{ Q' }} ->
      (Q' ->> Q) -> (* weakening of the postcondintion *)
      {{ P }} c {{ Q }}
  | H_PreStrengthening :
    forall (P Q P' : assertion) (c : com),
      {{ P' }} c {{ Q }} ->
      (P ->> P') -> (* strengthening of the precondintion *)
      {{ P }} c {{ Q }}
  | H_Assert :
    forall (P : assertion) (b : bexp),
      {{ P AND (TRUE b) }} <{ assert b }> {{ P AND (TRUE b)}}
  | H_Require :
    forall (P : assertion) (b : bexp),
      {{ P }} <{ require b }> {{ P AND (TRUE b) }}

  where "{{ P }} c {{ Q }}" := (triple P c Q) : hoare_spec_scope.

  (* [triple] grade 0/10 *)

  (** Για να ελέγξετε τους ορισμούς σας, αποδείξτε τα παρακάτω Hoare triples. *)

  Example require_example :
    forall Q, {{ fun _ => True }} require false {{ Q }}.
  Proof.
    intros Q.
    remember (fun _ => True) as P.
    eapply H_PreStrengthening; try eapply H_PostWeakening.
    - apply H_Require.
    - intros st H. destruct H as [H1 H2]. discriminate.
    - intros st H. apply HeqP.
  Qed.

  (* [require_example] grade 0/3 *)

  Example assert_example :
    {{ fun st => st X = 42 }} assert (X = 42) {{ fun _ => True }}.
  Proof.
    remember (fun _ => True) as P.
    remember (fun st => st X = 42) as Q.
    eapply H_PreStrengthening; try eapply H_PostWeakening.
    - apply H_Assert.
    - intros st H. rewrite HeqP. reflexivity.
    - intros st H. split.
      + apply HeqP.
      + unfold TRUE. simpl. apply Nat.eqb_eq. assumption.
  Qed.

  (* [assert_example] grade 0/3 *)

  Example require_assert :
    {{ fun st => True }}
      require (21 < X && 21 < Y);
      Z := X + Y;
      assert (42 < Z)
    {{ fun _ => True }}.
  Proof.
    remember (fun _ => True) as P.
    eapply H_PreStrengthening;
    try eapply H_PostWeakening;
    repeat eapply H_Seq.
    - apply H_Assert.
    - apply H_Asgn.
    - eapply H_PostWeakening.
      + apply H_Require.
      + intros st H. destruct H as [H1 H2]. unfold assertion_sub. simpl.
        split.
        * apply H1.
        * unfold TRUE in *. simpl in *. apply Nat.ltb_lt.
          apply andb_prop in H2. destruct H2 as [H2 H3]. apply Nat.ltb_lt in H2, H3.
          unfold update_st. simpl. lia.
    - intros st H. rewrite HeqP. reflexivity.
    - intros st H.
      remember ((Z !-> st X + st Y; st)) as st'.
      apply HeqP.
  Qed.

  (* [require_assert] grade 0/4 *)

  (** Σας δίνεται η απόδειξη συνέπειας της λογικής Hoare προσαρμοσμένη
      στη νέα σημασιολογία. Επεκτείνετέ την με τις περιπτώσεις για
      τους νέους κανόνες. *)

  Definition valid (P : assertion) (c : com) (Q : assertion) : Prop :=
    forall st res,
      st =[ c ]=> res ->                          (* if the program starting from [st] produces a result *)
      P st ->                                     (* and [st] satisfies [P] *)
      exists st', res = Success st' /\ Q st'.     (* then the result is a successful state [st'] that satisfies [Q]. *)

  Theorem hoare_triple_sound :
    forall (P Q : assertion) (c : com ),
      {{ P }} c {{ Q }} ->
      valid P c Q.
  Proof.
    unfold valid.
    intros P Q c Htriple.
    induction Htriple; intros st1 st2 Heval HP.
    - inv Heval; eauto.
    - inv Heval. eauto.
    - inv Heval.
      + edestruct IHHtriple1; eauto.
        edestruct IHHtriple2; eauto. inv H. congruence.
      + edestruct IHHtriple2; eauto. inv H. congruence.
    - inv Heval.
      + (* binterp st1 b = true *)
        eapply IHHtriple1; hoare_auto.
      + (* binterp st1 b = false *)
        eapply IHHtriple2; hoare_auto.
    - remember <{ while b do c }> as loop eqn:Heq.

      induction Heval; try congruence; inv Heq.
      + (* E_WhileFalse *) hoare_auto.
      + (* E_WhileTrue Success *)
        apply IHHeval2. reflexivity.
        edestruct IHHtriple; [ eassumption | hoare_auto | ].
        inv H0. congruence.
      + (* E_WhileTrue Error *)
        edestruct IHHtriple; [ eassumption | hoare_auto | ].
        inv H0. congruence.
    - edestruct IHHtriple; [ eassumption | hoare_auto | ].
      inv H. eauto.
    - edestruct IHHtriple; [ eassumption | hoare_auto | ].
      inv H. eauto.
    - inv Heval.
      + (* Success state *)
        exists st1. split.
        * reflexivity.
        * assumption.
      + (* Error state *)
        unfold assert_and in HP. destruct HP as [HP1 HP2].
        unfold TRUE in HP2. congruence.
    - inv Heval.
      (* only success state exists *)
      exists st1. split.
      + reflexivity.
      + hoare_auto.
  Qed.

  (* [hoare_triple_sound] grade 0/8 *)

  (* [hoare_triple_complete] grade 0/10 *)

End RequireAssert.

(** ** Άσκηση 3: Fast Exponentiation in Dafny (50 μονάδες) *)

  (** Συμπληρώστε το αρχείο [fastexp.dfy]. Θα πρέπει να γράψετε ένα
      πρόγραμμα Dafny που υπολογίζει την ύψωση σε δύναμη με τη μέθοδο
      του επαναλαμβανόμενου τετραγωνισμού. Το πρόγραμμα θα πρέπει να
      ικανοποιεί το δοσμένο postcondition, που δηλώνει ότι υπολογίζει
      σωστά την ύψωση σε δύναμη σε σχέση με τη συναρτησιακή
      προδιαγραφή [pow].

      Hint: Μπορείτε να γράψετε ένα λήμμα που να περιγράφει με τι
      ισούται η τιμή [pow(x,n)] στην περίπτωση που το [n] είναι άρτιος
      και στην περίπτωση που το [n] είναι περιττός. *)
