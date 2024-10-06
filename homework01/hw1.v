Require Import Coq.Init.Nat Coq.Bool.Bool.

(** Στοιχεία Σπουδαστή
Όνομα:  
ΑΜ: 
*)


(** * Εργασία 1 (100 μονάδες) *)

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

(** ** Άσκηση 1: Booleans (25 μονάδες) *)

(** Συμπληρώστε τον ορισμό μιας συνάρτησης που ελέγχει δύο booleans για ισότητα
    και επιστρέφει true αν τα δύο ορίσματα είναι ίσα και [false] διαφορετικα *)

Definition test_eq (b1 b2 : bool) : bool (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [test_eq] Grade: 0/5 *)

(** Αποδείξτε ότι ο ορισμός της [test_eq] είναι σωστός. Ότι δηλαδή η κλήση 
    [test_eq b1 b2] επιστρέφει [true] αν και μόνο αν [b1 = b2]. *)

Lemma test_eq_sound :
  forall b1 b2, test_eq b1 b2 = true -> b1 = b2. 
Proof. 
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [test_eq_sound] Grade: 0/10 *)

Lemma test_eq_complete :
  forall b1 b2, b1 = b2 -> test_eq b1 b2 = true. 
Proof. 
(*  ___ FILL IN HERE ___ *)
Admitted.

(* [test_eq_complete] Grade: 0/10 *)

(** ** Άσκηση 2: Φυσικοί αριθμοί στο δυαδικό σύστημα (25 μονάδες) *)

(** Σας δίνεται ένας επαγωγικός τύπος που αναπαριστά φυσικούς αριθμούς
    στο δυαδικό σύστημα. *)

Inductive bin : Type :=
| Z : bin
| B0 : bin -> bin
| B1 : bin -> bin.

(** Σε αυτή την αναπαράσταση, ένας αριθμός αναπαρίσταται ως μία
    ακολουθία ψηφίων [Β0] (συμβολίζει το 0) ή [Β1] (συμβολίζει το 1)
    που τερματίζονται απο το [Ζ] (συμβολίζει την κενή ακολουθία bits
    που αναπαριστά και το 0). Κατά σύμβαση, οι αριθμοί αναπαρίστανται
    με το least significant bit στα αριστερά (δηλαδή το αντίθετο από
    ότι συνήθως). Αυτό θα διευκολύνει τους ορισμούς μας.
    
    Για παράδειγμα, το 4 αναπαρίσταται ως εξής: *)

Definition four : bin := B0 (B0 (B1 Z)). 

(** Προθέρμανση: συμπληρώστε τους ακόλουθους αριθμούς. *)

Definition three : bin (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

Definition seven : bin (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

Definition eight : bin (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [num_defs] Grade: 0/3 *)

(** Γράψτε μια συνάρτηση που να μετατρέπει έναν αριθμό σε δυαδική
    αναπαράσταση σε έναν αριθμό σε μοναδιαία (unary) αναπαράσταση *)

Fixpoint bin_to_nat (b : bin) : nat (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [bin_to_nat] Grade: 0/8 *)

(** Sanity check: Τα παρακάτω θα πρέπει να επιτυγχάνουν εάν ο ορισμός
    της συνάρτησής σας είναι σωστός. Διαγράψτε τα [Admitted] και κάντε
    uncomment την απόδειξη.

    Σημείωση: To keyword [Example] είναι συνώνυμο του [Lemma].
*)

Example test_bin_to_nat : bin_to_nat seven = 7.
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_bin_to_nat' : bin_to_nat three = 3.
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_bin_to_nat'' : bin_to_nat (B0 (B1 (B1 Z))) = 6.
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_bin_to_nat''' : bin_to_nat (B1 (B1 (B0 (B0 Z)))) = 3.
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_bin_to_nat'''' : bin_to_nat (B1 (B1 (B0 Z))) = 3.
Admitted.
(* Proof. simpl. reflexivity. Qed. *)


(** Γράψτε μια συνάρτηση που να αυξάνει έναν δυαδικό αριθμό κατά ένα. *)

Fixpoint bin_incr (b : bin) : bin (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [bin_incr] Grade: 0/10 *)

(** Χρησιμοποιώντας την παραπάνω συνάρτηση, γράψτε μια συνάρτηση που
    μετατρέπει έναν αριθμό σε μοναδιαία (unary) αναπαράσταση σε έναν
    αριθμό σε δυαδική αναπαράσταση *)

Fixpoint nat_to_bin (n : nat) : bin (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [nat_to_bin] Grade: 0/4 *)

(** Sanity check: Τα παρακάτω θα πρέπει να επιτυγχάνουν εάν οι
    παραπάνω ορισμοί είναι σωστοί. Διαγράψτε τα [Admitted] και κάντε
    uncomment την απόδειξη. *)

Example test_nat_to_bin : nat_to_bin 7 = (B1 (B1 (B1 Z))).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_nat_to_bin' : nat_to_bin 6 = (B0 (B1 (B1 Z))).
Admitted.
(* Proof. simpl. reflexivity. Qed. *)

Example test_nat_to_bin'' : bin_to_nat (B1 (B1 (B0 Z))) = 3.
Admitted.
(* Proof. simpl. reflexivity. Qed. *)


(** ** Άσκηση 3: Πολλαπλασιασμός (25 μονάδες) *)

(** Η συνάρτηση βιβλιοθήκης [mul] ορίζει τον πολλαπλασιασμό. Ο ορισμός της
    είναι ο ακόλουθος. *)

Print mul. 

(** Η άσκηση σας ζητά να αποδείξετε τα  ακόλουθα απλά λήμματα σχετικά
    με τον πολλαπλασιασμό. Σημείωση: Για κανένα απο τα λήμματα δεν θα
    χρειαστεί να κάνετε απόδειξη με επαγωγή.  *)

(** Το παρακάτω λήμμα λέει ότι το [0] είναι το απορροφητικό στοιχείο
    του πολλαπλασιασμού. *) 

Lemma mul_zero_abs_l :
  forall (m : nat), 0 * m = 0.
Proof.
  (*  ___ FILL IN HERE ___ *)
Admitted.

(* [mul_zero_abs_l] Grade: 0/5 *)


(** Το παρακάτω λήμμα περιγράφει το αποτέλεσμα του πολλαπλασιασμού όταν το πρώτο
  όρισμα είναι ο successor ενός αριθμού. *) 
Lemma mul_Sm_n :
  forall (m n : nat), (S m) * n = n + m * n.
Proof.
  (*  ___ FILL IN HERE ___ *)
Admitted.

(* [mul_Sm_n] Grade: 0/5 *)

(** Αποδείξτε ότι αν δύο ζεύγη αριθμών είναι ίσα, τότε και
    τα γινόμενα τους θα είναι ίσα. *)

Lemma mul_preserves_eq :
  forall (n1 n2 m1 m2 : nat),
    n1 = n2 ->
    m1 = m2 ->
    n1 * m1 = n2 * m2. 
Proof.
  (*  ___ FILL IN HERE ___ *)
Admitted.

(* [mul_preserves_eq] Grade: 0/5 *)


(** Χρησιμοποιήστε την [mul] για να γράψετε μια συνάρτηση [exp] που
    υψώνει το πρώτο της όρισμα [base] στην δύναμη πού δίνεται από το
    δεύτερο όρισμα, [power] *) 

Fixpoint exp (base power : nat) : nat (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)


(** Αποδείξτε το παρακάτω λήμμα που περιγράφει την ύψωση σε δύναμη, όταν ή δύναμη είναι
    ο successor ενός αριθμού. *)

Lemma exp_base_Spower :
  forall base power, exp base (S power) = base * exp base power.
Proof.
  (*  ___ FILL IN HERE ___ *)
Admitted.

(* [exp_base_Spower] Grade: 0/5 *)


(** ** Άσκηση 4: Booleans, ξανά (25 μονάδες) *)

(** Αποδείξτε το νόμο de Morgan για την άρνηση της λογικής σύζευξης. *)

Lemma de_morgan_law_or :
  forall (x y : bool), (* universal quantifier *)
    negb (x && y) = (negb x) || (negb y).
Proof.
    (*  ___ FILL IN HERE ___ *)
Admitted.

(* [de_morgan_law_or] Grade: 0/5 *)

(** Αποδείξτε ότι η λογικής σύζευξη είναι αντιμεταθετική. *)
Lemma and_commutative :
  forall (x y : bool), (* universal quantifier *)
    x && y = y && x.
Proof.
    (*  ___ FILL IN HERE ___ *)
Admitted.

(* [and_commutative] Grade: 0/5 *)


(** Ορίστε μια συνάρτηση που να υπολογίζει την αποκλειστική διάζευξη. *)

Definition xor (b1 b2 : bool) : bool (* :=   ___ FILL IN HERE ___. *)
. Admitted. (* Διαγράψτε αυτή τη γραμμή και συμπληρώστε την από πάνω *)

(* [xor] Grade: 0/5 *)


(** Αποδείξτε ότι η αποκλειστική διάζευξη δύο τιμών είναι αληθείς όταν
    ισχύει μία απο τις δύο τιμές, αλλά όχι και οι δύο ταυτόχρονα. *) (*  *)
Lemma xor_correct :
  forall (x y : bool), (* universal quantifier *)
    xor x y = (x || y) && (negb (x && y)).
Proof.
    (*  ___ FILL IN HERE ___ *)
Admitted.

(* [xor_correct] Grade: 0/10 *)
