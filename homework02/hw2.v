Require Import Coq.Init.Nat Coq.Arith.Arith Coq.Lists.List.
Import ListNotations. 

(** Στοιχεία Σπουδαστή
Όνομα: ΔΗΜΗΤΡΙΟΣ ΓΕΩΡΓΟΥΣΗΣ
ΑΜ: 03119005
*)


(** * Εργασία 2 (100 μονάδες + 10 μονάδες bonus) *)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με συναρτησιακό
    προγραμματισμό και την ανάπτυξη αποδείξεων στο Coq Proof Assistant.

    Οδηγίες:

    - Μπορείτε να χρησιμοποιείτε μόνο τα tactics που έχουμε κάνει στο μάθημα.  

    - Δεν μπορείτε να χρησιμοποιήσετε θεωρήματα απο την βιβλιοθήκη, εκτός και αν
      αυτό υποδεικνύεται από την άσκηση.

    - Εάν κολλήσετε σε κάποιο ενδιάμεσο lemma ή proof goal, μπορείτε να
      χρησιμοποιήσετε [admit] ώστε ολοκληρώσετε την άσκηση και να βαθμολογηθείτε
      για ότι έχετε λύσει.
    
    - To παραδοτέο αρχείο θα πρέπει να κάνει compile. Αυτό μπορείτε να το ελέγεξετε 
      στο terminal σας με την εντολή `coqc hw.1`. Τα αρχεία που δεν κάνουν compile 
      δεν θα βαθμολογούνται.

    - Όταν ολοκληρώνετε κάποια απόδειξη, αντικαταστήστε το τελικό [Admitted] με
      [Qed].

    - Μην αλλάζετε τον κώδικα και το κείμενο που σας έχουν δωθεί. Μην γράφετε
      μέσα στα στα σχόλια της βαθμολόγησης. Αυτό είναι απαραίτητο για την ομαλή
      και έγκαιρη βαθμολόγηση των εργασιών. Μπορείτε να γράψετε όπου υπάρχει η
      οδηγία (*  ___ FILL IN HERE ___ *). Εάν σας εξυπηρετεί, μπορείτε
      να ορίζετε βοηθητικές συναρτήσεις, λήμματα, ορισμούς, κ.α.
      
    - Συμπληρώστε σωστά τα στοιχεία σας στην αρχή του αρχείου. Αυτό είναι 
      απαραίτητο για την σωστή βαθμολόγηση των εργασιών. *)


(** ** Άσκηση 1: Σύνθεση Συναρτήσεων (5 μονάδες) *)

(** Συμπληρώστε τον ορισμό μιας συνάρτησης που παίρνει ως ορίσματα δύο
    συναρτήσεις και επιστρέφει τη σύνθεσή τους. *)

Definition comp {A B C : Type} (f : A -> B) (g : B -> C) : A -> C :=
  fun (a : A) => g (f a).

(* [comp] Grade: 0/1 *)


(** Συμπληρώστε τον ορισμό του κατηγορήματος (predicate) που δηλώνει
    ότι μια συνάρτηση να είναι ένα-προς-ένα (injective). *)

Definition injective {A B : Type} (f : A -> B) : Prop :=
  forall a b, f a = f b -> a = b.

(* [injective] Grade: 0/1 *)

(** Αποδείξτε ότι η σύνθεση συναρτήσεων που είναι ένα-προς-ένα, είναι
    και αυτή μια ένα-προς-ένα συνάρτηση.

    Αντικαταστήστε το [False] με τη σωστή διατύπωση. *)

Theorem comp_injective :
  forall A B C (f : A -> B) (g : B -> C), injective f -> injective g -> injective (comp f g).
Proof. 
  intros A B C f g Hf Hg.
  unfold injective.

  intros a b H.
  unfold comp in H.
  unfold injective in Hf, Hg.
  specialize Hf with (a := a) (b := b).
  apply Hf.
  specialize Hg with (a := f a) (b := f b).
  apply Hg. assumption.
Qed.



(* [comp_injective] Grade: 0/3 *)


(** ** Άσκηση 2: Φυσικοί αριθμοί στο δυαδικό σύστημα (30 μονάδες) *)

(** Σας δίνεται ένας επαγωγικός τύπος που αναπαριστά φυσικούς αριθμούς
    στο δυαδικό σύστημα καθώς και οι ορισμοί [bin_to_nat], [bin_incr]
    και [nat_to_bin] από την προηγούμενη άσκηση. *)

Inductive bin : Type :=
| Z : bin
| B0 : bin -> bin
| B1 : bin -> bin.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
  | Z => 0
  | B0 x => 2 * bin_to_nat x
  | B1 x => 1 + 2 * bin_to_nat x
  end.

Fixpoint bin_incr (b : bin) : bin :=
  match b with
  | Z => B1 Z
  | B0 x => B1 x
  | B1 x => B0 (bin_incr x)
  end.

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S x => bin_incr (nat_to_bin x)
  end.


(** Αποδείξτε ότι, για κάθε δυαδικό αριθμό, η αύξηση του κατά ένα και
    στη συνέχεια η μετατροπή του σε μοναδιαίο φυσικό αριθμό, δίνει το
    ίδιο αποτέλεσμα με τη μετατροπή του σε μοναδιαίο αριθμό και στη
    συνέχεια την αύξηση αυτού του μοναδιαίου αριθμού κατά ένα. *)

(** Μπορείτε να χρησιμοποιήσετε τα θεωρήματα βιβλιοθήκης [plus_n_O]
    και [plus_n_Sm]. Καθώς το συμπέρασμα των θεωρημάτων αυτών είναι
    μία ισότητα, μπορείτε να τα χρησιμοποιήσετε με το tactic [rewrite].
    
    Π.χ. [rewrite plus_n_O] ή [rewrite <- plus_n_O] *)

Check plus_n_O.
Check plus_n_Sm.

Lemma bin_to_nat_pres_incr :
  forall b : bin, bin_to_nat (bin_incr b) = 1 + (bin_to_nat b).
Proof.
  intros b.
  induction b.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IHb. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

(* [bin_to_nat_pres_incr] Grade: 0/20 *)

(** Χρησιμοποιώντας το παραπάνω λήμμα, αποδείξτε ότι για κάθε δυαδικό
    αριθμό, η μετατροπή του σε μοναδιαίο αριθμό και στη συνέχεια η
    μετατροπή του αποτελέσματος ξανά σε δυαδικό επιστρέφει τον αρχικό
    αριθμό. Δηλαδή, ότι η σύνθεση των συναρτήσεων [bin_to_nat] και
    [nat_to_bin] είναι η ταυτοτική συνάρτηση. *)

Theorem nat_bin_nat :
  forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n.
  - reflexivity.
  - simpl. rewrite bin_to_nat_pres_incr. simpl. rewrite IHn. reflexivity.
Qed.


(* [nat_bin_nat] Grade: 0/10 *)



(** ** Άσκηση 3: Λογική (20 μονάδες) *)

(** Όπως αναφέραμε στο μάθημα, o νόμος της εξάλειψης της διπλής
    άρνησης (double negation elimination) είναι ισοδύναμος με το νόμο
    του αποκλειόμενου μέσου (excluded middle). Η άσκηση αυτή σας
    ζητάει να αποδείξετε και τυπικά αυτό το ισχυρισμό και σας
    καθοδηγεί ώστε να αποδείξετε τα απαραίτητα ενδιάμεσα λήμματα. *)

(** Θα χρειαστεί να αποδείξουμε τον νόμο του De Morgan για την άρνηση
    μιας λογικής διάζευξης.

    Παρατηρήστε ότι το tactic [auto] βρίσκει κατευθείαν την
    απόδειξη. Η άσκηση σας ζητά να μην χρησιμοποιήσετε [auto] αλλά να
    βρείτε την απόδειξη με χρησιμοποιόντας τα tactics [intros],
    [apply], [split], [left], [right], [assumption]. *)

Lemma de_morgan_or :
  forall (A B : Prop), ~ (A \/ B) -> ~ A /\ ~ B. 
Proof.
  intros A B H.
  split; intros P.
  - apply H. left. assumption.
  - apply H. right. assumption.
Qed.  


(* [de_morgan_or] Grade: 0/3 *)

(** Χρησιμοποιώντας το παραπάνω λήμμα, δείξτε ότι ισχύει η διπλή άρνηση του
    απολυόμενου μέσου. *)

Lemma not_not_EM : forall P, ~~ (P \/ ~ P).
Proof.
  intros P H.
  apply H.
  apply de_morgan_or in H.
  destruct H as [H H'].
  right. assumption.
Qed.

(* [not_not_EM] Grade: 0/3 *)


(** Για ευκολία, ορίζουμε τις δύο λογικές προτάσεις ώστε να μπορούμε 
    να αναφερόμαστε σε αυτές με ονόματα. *)

Definition DNE : Prop := forall P, ~~ P -> P. 

Definition EM : Prop := forall P, P \/ ~P. 


(** Μπορούμε τώρα να αποδείξουμε τον ισχυρισμό ότι οι δύο λογικές
    προτάσεις είναι ισοδύναμες. Για κάθε μια απο τις δύο κατευθύνσεις
    θα πρέπει να χρησιμοποιήσετε την υπόθεση κάνοντας την instantiate
    με την κατάλληλη λογική πρόταση στη θέση του καθολικά
    ποσοτικοποιημένου [P]. Αυτή η πρόταση θα είναι διαφορετική σε κάθε
    μία από τις δύο περιπτώσεις.

    Hint: Αυτό μπορείτε να το κάνετε είτε με το tactic [specialize H with (n := p)]
    είτε με το tactic [apply H with (P := p)] (χρησιμοποιόντας τα κατάλληλα
    [H], [P] και [p]) όπως είδαμε στο logic.v *)

Theorem DNE_EM : DNE <-> EM.
Proof.
  unfold DNE, EM.
  
  (* Θυμηθείτε ότι η ισοδυναμία ορίζεται ως σύζευξη δύο
     συνεπαγωγών. Μπορούμε λοιπόν να χρησιμοποιήσουμε το tactic
     [split] ώστε να δουλέψουμε ξεχωριστά με κάθε συνεπαγωγή. *) 
  split.
  
  - (* DNE -> EM *)
    intros H P.
    specialize H with (P := P \/ ~ P).
    apply H.
    apply not_not_EM.
    (* Hint: χρησιμοποιήστε το λήμμα [not_not_EM]. *)
    
  - (* EM -> DNE *)
    intros H P Hnn.
    specialize H with (P := P).
    destruct H.
    + assumption.
    + contradiction.
Qed.

(* [DNE_EM] Grade: 0/5 *)


(** Προσπαθήστε να δείξετε το νόμο του De Morgan για τη λογική
    σύζευξη. Τι παρατηρείτε; Γιατί συμβαίνει αυτό; *)

Lemma de_morgan_and :
  forall (A B : Prop), ~ (A /\ B) -> ~ A \/ ~ B. 
Proof.
  intros A B H.
  left. intros HA. apply H. split.
  - assumption.
  - assert (forall X Y, X -> ~ (X /\ Y) -> ~ Y) as H'.
    {
      intros X Y H1 H2 H3. apply H2. split; assumption.
    }
    specialize H' with (X := A) (Y := B).
    Fail apply H'.
Abort.

(** Σύντομη απάντηση: Στην παραπάνω απόπειρα απόδειξης αν αρχικά κάναμε 'right'.
    Θα παίρναμε παρόμοιο αποτέλεσμα, λόγω συμμετρίας. Χρειαζόμαστε κάποιον τρόπο
    να διώξουμε την διπλή άρνηση, το οποίο ισοδυναμεί με το να χρησιμοποιήσουμε
    το EM. Αναμένουμε η απόδειξη να είναι δυνατή με αυτό. *)

(* [de_morgan_and] Grade: 0/4 *)

(** Αποδείξτε τώρα το ίδιο λήμμα, υποθέτοντας τον νόμο του αποκλειόμενου μέσου. *)

Lemma de_morgan_and_ΕΜ :
  EM ->
  forall (A B : Prop), ~ (A /\ B) -> ~ A \/ ~ B.
Proof.
  intros HEM A B H.
  unfold EM in HEM.
  specialize HEM with (P := A).
  destruct HEM as [HA | HA].
  - right. intros HB. apply H. split; assumption.
  - left. assumption.
Qed.

(* [de_morgan_and_ΕΜ] Grade: 0/5 *)



(** ** Άσκηση 4: Λίστες (50 μονάδες) *)

(** Γράψτε μία επαγωγική σχέση (inductive relation), που να ισχύει όταν 
    ένα στοιχείο τύπου [Α] ανοίκει σε μία λίστα τύπου [list A].
*)

Inductive In {A : Type} (x : A) : list A -> Prop := 
  | In_head : forall l, In x (x :: l)
  | In_tail : forall y l, In x l -> In x (y :: l).

(* [In] Grade: 0/2 *)


(** Αποδείξτε ότι για κάθε συνάρτηση (f : A -> B) εάν ένα στοιχείο (x : A)
    ανοίκει σε μία λίστα [l], τότε το στοιχείο [f x] θα ανοίκει στην λίστα [map f l]. *)

Lemma In_map : 
 forall (A B : Type) (x : A) (l : list A) (f : A -> B),  
    In x l -> In (f x) (map f l). 
Proof. 
  intros A B x l f H.
  induction H.
  - simpl. left.
  - simpl. right. apply IHIn.
Qed.  

(* [In_map] Grade: 0/2 *)


(** Γράψτε μία συνάρτηση [fold_left] πολυμορφική στους τύπους [Α] και
    [Β], που παίρνει ως όρισμα μία συνάρτηση [f : A -> B -> A], μια
    λίστα [l : list B] και μια αρχική τιμή [a0 : A].

    Εάν η λίστα είναι ή [[x1; x2 ...; xn]] τότε το αποτέλεσμα της
    συνάρτησης είναι το [f (... (f (f a0 x1) x2)...) xn]. Η συνάρτηση
    επιστρέφει το [a0] εάν η λίστα είναι η κενή.

    Δηλαδή, η συνάρτηση εφαρμόζει διαδοχικά την [f] σε κάθε στοιχείο
    της λίστας, ξεκινώντας από το πρώτο (αριστερό) στοιχείο και
    χρησιμοποιώντας ως πρώτο όρισμα το [a0]. Το αποτέλεσμα της
    εφαρμογής της [f] σε ένα στοιχείο χρησιμοποιείται ως πρώτο όρισμα
    στην επόμενη εφαρμογή της [f] στο επόμενο στοιχείο της λίστας. *)

(** Σημείωση: To annotation [{struct l}] λέει στο Coq ποίο είναι το
    αναδρόμικό όρισμα μιας συνάρτησης. Σε αυτή την περίπτωση είναι
    απαραίτητο για τεχνικούς λόγους ώστε το Coq να αποδεχτεί τον
    [Αdmitted] ορισμό χωρίς το σώμα της συνάρτησης. *)


Fixpoint fold_left {A B} (f : A -> B -> A) (l : list B) (a0 : A) {struct l} : A :=
  match l with
  | [] => a0
  | hd :: tl => fold_left f tl (f a0 hd)
  end.


(* [fold_left] Grade: 0/2 *)

(** Προθέρμανση: χρησιμοποιήστε την [fold_left] για να γράψετε μία συνάρτηση [length] *)

Definition length (l : list nat) : nat :=
  fold_left (fun a0 _ => 1 + a0) l 0.

(* [length] Grade: 0/0.5 *)

Example test_length : length [1;2;3;4] = 4. 
Proof. reflexivity. Qed.

(** Προθέρμανση: χρησιμοποιήστε την [fold_left] για να γράψετε μία συνάρτηση που
    αθροίζει τα στοιχεία μιας λίστας φυσικών αριθμών *)
Definition sum (l : list nat) : nat :=
  fold_left (fun a0 x => x + a0) l 0.


(* [sum] Grade: 0/0.5 *)

Example test_sum : sum [1;2;3;4] = 10. 
Proof. reflexivity. Qed.



(** Αποδείξτε ότι αν μια συνάρτηση [f : A -> A -> A] είναι αντιμεταθετική και
    προσεταιριστική τότε για κάθε λίστα [l], αρχική τιμή [a0] και τιμή [a], ισχύει:

              [f (fold_left f l a0) a = fold_left f l (f a0 a)] 

    Για να αποδείξετε αυτό τον ισχυρισμό είναι πολύ σημαντικό να έχετε μια
    επαρκώς γενική επαγωγική υπόθεση. Θυμηθείτε ότι μπορείτε να γενικεύετε
    μεταβλητές που βρίσκονται στο proof context με το tactic [revert].

    Αντικαταστήστε το [False] με τη σωστή διατύπωση.
*)


Definition assoc {A : Type} (f : A -> A -> A) :=
  forall (x y z: A), f (f x y) z = f x (f y z).

Definition comm {A : Type} (f : A -> A -> A) :=
  forall (x y: A), f x y = f y x.

Theorem fold_left_assoc_comm :
  forall A (f : A -> A -> A), assoc f -> comm f ->
  (forall (l : list A) (a0 : A) (a : A), f (fold_left f l a0) a = fold_left f l (f a0 a)).
Proof.
  intros A f Hassoc Hcomm.
  unfold assoc, comm in Hassoc, Hcomm.
  induction l.
  - intros. simpl. reflexivity.
  - intros. simpl.
    rewrite Hcomm with (x := a0) (y := a1).
    rewrite Hassoc with (x := a1) (y := a0) (z := a).
    rewrite Hcomm with (x := a1) (y := f a0 a).
    apply IHl with (a0 := f a0 a) (a := a1).
Qed.

(* [fold_left_assoc_comm] Grade: 0/25 *)


(** Γράψτε μία συνάρτηση fold_right πολυμορφική στους τύπους Α και Β,
    που παίρνει ως όρισμα μία συνάρτηση [f : B -> A -> A], μια λίστα
    [l] και μια αρχική τιμή [a0].

    Εάν η λίστα είναι ή [[x1; ...; xn]] τότε το αποτέλεσμα της
    συνάρτησης είναι το [f x1 (f x2 (... (f xn a0))))]. Η συνάρτηση
    επιστρέφει το [a0] εάν η λίστα είναι η κενή.

    Δηλαδή, η συνάρτηση εφαρμόζει διαδοχικά την [f] σε όλα τα στοιχεία
    της λίστας, ξεκινώντας από το τελευταίο (δεξιό) στοιχείο,
    χρησιμοποιώντας ως δεύτερο όρισμα το [a0]. Το αποτέλεσμα της
    εφαρμογής της [f] σε ένα στοιχείο χρησιμοποιείται ως δεύτερο
    όρισμα στην επόμενη εφαρμογή της [f] στο προηγούμενο στοιχείο
    της λίστας. *)

Fixpoint fold_right {A B} (f : B -> A -> A) (l : list B) (a0 : A) {struct l} : A  :=
  match l with
  | [] => a0
  | hd :: tl => f hd (fold_right f tl a0)
  end.

(* [fold_right] Grade: 0/2 *)

(** Προθέρμανση: χρησιμοποιήστε την [fold_right] για να γράψετε μία συνάρτηση [length'] *)

Definition length' (l : list nat) : nat :=
  fold_right (fun _ a0 => 1 + a0) l 0.

(* [length'] Grade: 0/0.5 *)

Example test_length' : length' [1;2;3;4] = 4.
Proof. reflexivity. Qed.

(** Προθέρμανση: χρησιμοποιήστε την [fold_right] για να γράψετε μία
    συνάρτηση που αθροίζει τα στοιχεία μιας λίστας φυσικών αριθμών *)

Definition sum' (l : list nat) : nat :=
  fold_right (fun x a0 => x + a0) l 0.

(* [sum'] Grade: 0/0.5 *)

Example test_sum' : sum' [1;2;3;4] = 10. 
Proof. reflexivity. Qed.

(** Αποδείξτε ότι αν μια συνάρτηση [f : A -> A -> A] είναι
    αντιμεταθετική και προσεταιριστική τότε για κάθε λίστα [l] και αρχική
    τιμή [a0], ισχύει:

                  [fold_right f l a0 = fold_left f l a0]

    Αντικαταστήστε το [False] με τη σωστή διατύπωση. *)

(** Σημείωση: Για να αποδείξετε το παρακάτω θεώρημα θα χρειαστεί να
    χρησιμοποιήσετε το λήμμα [fold_left_assoc_comm]. Καθώς το
    συμπέρασμα του λήμματος είναι μια ισότητα μπορείτε να το
    χρησιμοποιήσετε με το [rewrite] tactic. Όταν το κάνετε αυτό το Coq
    θα σας ζητήσει να αποδείξετε όλες τις προϋποθέσεις (premises) του
    λήμματος. *)

Theorem fold_left_fold_right :
  forall A (f : A -> A -> A), assoc f -> comm f ->
  (forall (l : list A) (a0 : A), fold_right f l a0 = fold_left f l a0).
Proof. 
  intros A f Hassoc Hcomm l a0.
  induction l.
  - simpl. reflexivity.
  - simpl. rewrite IHl.
    unfold comm in Hcomm.
    rewrite Hcomm with (x := a) (y := fold_left f l a0).
    rewrite fold_left_assoc_comm.
    + reflexivity.
    + assumption.
    + unfold comm. assumption.
Qed.

(* [fold_left_fold_right] Grade: 0/10 *)


(** Γράψτε μία συνάρτηση [foo : A -> A -> A] για κάποιο τύπο [Α] της
    επιλογής σας για τον οποίο οι συναρτήσεις [fold_left] και
    [fold_right] επιστρέφουν διαφορετικά αποτελέσματα όταν
    εφαρμόζονται στην ίδια λίστα και στην ίδια αρχική τιμή. Τι
    χαρακτηριστικά έχει αυτή η συνάρτηση; Γράψτε δύο παραδείγματα, στο
    πρότυπο των [test_sum] και [test_sum'] που να δείχνουν ότι η
    συνάρτηση επιστρέφει διαφορετικό αποτέλεσμα. *)

Definition foo x y := x - y. (** Χρησιμοποιήσαμε ως Α το nat *)

Example fold_left_fold_right_different :
  fold_left foo [4;3;2;1] 0 = fold_right foo [4;3;2;1] 0 -> False.
Proof. simpl. intros H. discriminate H. Qed.

Example fold_left_fold_right_different' :
  fold_left foo [10;7;3;1] 0 = fold_right foo [10;7;3;1] 0 -> False.
Proof. simpl. intros H. discriminate H. Qed.

(** Η συνάρτηση foo() είναι η πράξη της αφαίρεσης στους nat.
    Η αφαίρεση δεν έχει την αντιμεταθετική ιδιότητα. Συνεπώς,
    τα fold_left() και fold_right() σε ίδια λίστα δεν δίνουν εγγυημένα
    το ίδιο αποτέλεσμα. Πράγμα που επαληθεύουμε με τα παραδείγματά μας.
*)

(* [fold_left_fold_right_different] Grade: 0/5 *)
