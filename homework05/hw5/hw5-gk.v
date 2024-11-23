Require Import Coq.Strings.String Coq.Init.Nat Coq.Lists.List.

Require Import miniML.

Import MiniML. 
Import ListNotations.

(** Στοιχεία Σπουδαστή
Όνομα: Γεώργιος Αλέξιος Καπετανάκης
ΑΜ: 03119062
*)

(** * Εργασία 5 (100 μονάδες) *)

(** Ο σκοπός αυτής της εργασίας είναι να εξοικειωθείτε με ένα κεντρικό
    θέμα της υλοποίησης των συναρτήσεων υψηλής τάξης, τα function
    closures.

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


(** ** Άσκηση 1: Interpreter για miniML (50 μονάδες) *)

(** Για τον ορισμό της σημασιολογίας του λάμδα λογισμού και την
    υλοποίηση του διερμηνέα για τη MiniML, χρησιμοποιήσαμε ένα μοντέλο
    εκτέλεσης που βασίζεται στην αντικατάσταση των τυπικών παραμέτρων
    των συναρτήσεων με τις τιμές πραγματικών παραμέτρων κατά την κλήση
    μίας συνάρτησης.

    Ωστόσο, αυτό το μοντέλο δεν είναι το πλέον πρακτικό για την
    υλοποίηση των συναρτήσεων. Η αντικατάσταση μεταβλητών είναι μια
    διαδικασία που απαιτεί την διάσχιση του κώδικα της συνάρτησης σε
    κάθε κλήση, μειώνοντας την αποδοτικότητα, και επιπλέον απαιτεί
    τροποποίηση του κώδικα μιας συνάρτησης κατά την εκτέλεση.

    Μια πιο αποτελεσματική προσέγγιση, η οποία ανταποκρίνεται καλύτερα
    στην υλοποίηση συναρτήσεων υψηλής τάξης, είναι η χρήση ενός
    περιβάλλοντος που αντιστοιχεί τις μεταβλητές στις τιμές τους. Με
    αυτό τον τρόπο, η τιμή μιας μεταβλητής αναζητείται στο περιβάλλον
    μόνο όταν χρειάζεται.

    Στην MiniML, όπως και στις γλώσσες με συναρτήσεις υψηλής τάξης, οι
    συναρτήσεις είναι πρώτης τάξης οντότητες (first-class
    citizens). Αυτό σημαίνει ότι οι συναρτήσεις μπορούν να
    χρησιμοποιηθούν ως τιμές, να περάσουν ως παράμετροι σε άλλες
    συναρτήσεις, να επιστραφούν από συναρτήσεις, ή να αποθηκευτούν σε
    μεταβλητές.

    Κατά τον ορισμό της όμως, μια συνάρτηση μπορεί να αναφέρεται σε
    μεταβλητές που είναι ορισμένες σε κάποια εξωτερική εμβέλεια μιας
    περιβάλλουσας συνάρτησης. Σύμφωνα με τους κανόνες στατικής εμβέλειας
    (lexical scoping), αυτές οι ελεύθερες μεταβλητές, κατά την κλήση
    της συνάρτησης, θα πρέπει να έχουν τις τιμές που είχαν όταν
    ορίστηκε η συνάρτηση.

    Για παράδειγμα, στο παρακάτω πρόγραμμα:

    << let foo = fun x ->
         let bar = fun y -> x + y in
         bar
     in
     let baz = foo 11 in
     baz 42 >>

    Όταν η συνάρτηση bar κληθεί, μέσω της κλήσης της baz, η ελεύθερη
    μεταβλητή x θα πρέπει να υπάρχει στο περιβάλλον με την τιμή 11.

    Για να επιτευχθεί αυτό, η τιμή μιας συνάρτησης σε αυτό το μοντέλο
    εκτέλεσης δεν είναι μόνο ο κώδικας της, αλλά ένα ζεύγος που
    αποτελείται από τον κώδικα της (δηλαδή τον ορισμό της) και το
    περιβάλλον που περιέχει τις τιμές των ελεύθερων μεταβλητών
    της κατά τον ορισμό της. Αυτή η δομή ονομάζεται closure. *)

(** H άσκηση σας ζητά να προσαρμόσετε τον διερμηνέα της MiniML από τις
    σημειώσεις του μαθήματος ώστε να ακολουθεί ένα μοντέλο εκτέλεσης
    με χρήση περιβάλλοντος.

    Το περιβάλλον είναι ένα key-value map, το οποίο αντιστοιχεί
    μεταβλητές στις τιμές τους. Οι μεταβλητές στο περιβάλλον
    περιλαμβάνουν είτε τις τυπικές παραμέτρους των συναρτήσεων είτε
    μεταβλητές που δεσμεύονται από εντολές let.

    Για ευκολία, στην άσκηση το περιβάλλον υλοποιείται ως λίστα με
    key-value ζεύγη, αλλά θα μπορούσαμε να επιλέξουμε κάποια πιο
    αποδοτική δομή (π.χ. AVL trees)

    Σημείωση: H ΜiniML της άσκησης έχει επεκταθεί με tuples αντί για
    ζεύγη που έχει η ΜiniML στις διαλέξεις. Μπορείτε να δείτε τον
    ορισμό τους στο συνοδευτικό αρχείο miniML. H concrete σύνταξη τους
    είναι {t1, ... , tn} για ένα tuple με n στοιχεία, και t # n για την
    εξαγωγή του n-οστού στοιχείου από ένα tuple.

    Οι constructors που τους αντιστοιχούν είναι:

    T_Tuple : list term -> term (* tuple constructor *)
    T_Proj : nat -> term -> term (* projection *)
*)

(** Σας δίνεται το interface για τα περιβάλλοντα υλοποιημένα με λίστες. *)

Definition var_map (A : Type) : Type := list (string * A).

Definition empty {A} : var_map A := [].

Definition lookup {A} (var : string) (env : var_map A) : option A :=
  match find (fun '(x, _) => String.eqb x var) env with
  | Some (_, v) => Some v
  | None => None
  end.

Definition add {A} (var : string) (val : A) (env : var_map A) : var_map A :=
  (var, val) :: env. 

(** Οι τιμές στις οποίες μπορεί να αποτιμηθεί ένα όρος είναι οι εξής *)

Inductive value : Type :=
(* Closure *)
| V_Clo :
  var_map value ->  (* Το περιβάλλον του closure *)
  string -> term -> (* Η συνάρτηση *)
  value
(* Natural Numbers *)
| V_Nat : nat -> value
(* Booleans *)
| V_Bool : bool -> value
(*  Tuples *)
| V_Tuple : list value -> value. 

(** Ένα περιβάλλον αντιστοιχεί ονόματα μεταβλητών στις τιμές τους. *)

Definition environment : Type := var_map value.

(** Auxillary function *)
Fixpoint map_error {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | h :: tl =>
    match f h with
    | Some x =>
      match map_error f tl with
      | Some xs => Some (x :: xs)
      | None => None
      end
    | None => None
    end
  end.

(** Συμπληρώστε τον παρακάτω interpreter. *)

Fixpoint eval (fuel : nat) (env : environment) (t : term) : option value :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match t with
      (* Application *)
      | <[ t1 t2 ]> =>
        match eval fuel' env t1 with
        (* <[ fun x -> t ] *)
        | Some (V_Clo env' x t) =>
          match eval fuel' env t2 with
          | Some v => eval fuel' (add x v env') t
          | None => None
          end
        (* If t1 does not evaluate to a lambda function
        then the application term is ill-formed *)
        | _ => None
        end
      (* Let *)
      | <[ let x := t1 in t2 ]> =>
        match eval fuel' env t1 with
        | Some v => eval fuel' (add x v env) t2
        | None => None
        end
      (* If *)
      | <[ if t1 then t2 else t3 ]> =>
        match eval fuel' env t1 with
        | Some (V_Bool true) => eval fuel' env t2
        | Some (V_Bool false) => eval fuel' env t3
        | _ => None
        end
      (* Bop *)
      | T_BOp bop t1 t2 =>
        match eval fuel' env t1, eval fuel' env t2 with
        | Some (V_Bool b1), Some (V_Bool b2) =>
          match bop with
          | And => Some (V_Bool (b1 && b2))
          | Or => Some (V_Bool (b1 || b2))
          | _ => None
          end
        | Some (V_Nat n1), Some (V_Nat n2) =>
          match bop with
          | Plus => Some (V_Nat (n1 + n2))
          | Minus => Some (V_Nat (n1 - n2))
          | Mult => Some (V_Nat (n1 * n2))
          | Lt => Some (V_Bool (n1 <? n2))
          | Eq => Some (V_Bool (n1 =? n2))
          | _ => None
          end
        | _, _ => None
        end
      (* UOp *)
      | T_UOp op t =>
        match eval fuel' env t with
        | Some (V_Bool b) =>
          match op with
          | Neg => Some (V_Bool (negb b))
          end
        | _ => None
        end
      (* Tuple *)
      | T_Tuple ts =>
        match map_error (eval fuel' env) ts with
        | Some vs => Some (V_Tuple vs)
        | None => None
        end
      | T_Proj n t =>
        match eval fuel' env t with
        | Some (V_Tuple vs) =>
          match nth_error vs n with
          | Some v => Some v
          | None => None
          end
        | _ => None
        end
      (* Values *)
      | <[ fun x -> t ]> => Some (V_Clo env x t)
      | T_Nat n => Some (V_Nat n)
      | T_Bool b => Some (V_Bool b)
      | T_Var x => lookup x env
    end
  end.

(** Top-level ορισμός για την αποτίμηση ενός προγράμματος στο κενό περιβάλλον. *)

Definition eval_top (fuel : nat) (t : term) : option value :=
  eval fuel empty t. 

(** Εάν ο ορισμός σας είναι σωστός τα παρακάτω tests θα πρέπει να επιτυγχάνουν. *)

Definition test1 : term := <[ let f := (fun x -> x + 4) in f 4 ]>.
Definition test2 : term := <[ let foo := (fun x -> x + 7) in
                              let bar := (fun x -> x * 2) in
                              (foo (bar 4)) ]>.
Definition test3 : term :=
  <[ let foo := fun n -> if n = 0 then 0 else n * n in foo 4]>.

Definition test4 : term := <[ let foo :=
                                (fun x ->
                                     let bar := fun y -> x + y in bar) in
                              foo 7 8 ]>.

(* my test *)
Definition test5 : term := <[
  let f := fun x ->
    let x := x + 1 in
    let y := 2 in
    let foo := fun y ->
      x + y in
    let bar := fun n -> 
      let fact := x + y + n in
      fact in
    foo (bar 10) in
  f 0
]>.

Definition myfact : term :=
  <[ letrec fact := fun n -> if n = 0 then 1 else n * fact (n - 1) in fact 5 ]>.

Example example1 : eval_top 1000 test1 = Some (V_Nat 8).
Proof. reflexivity. Qed.

Example example2 : eval_top 1000 test2 = Some (V_Nat 15).
Proof. reflexivity. Qed.

Example example3 : eval_top 1000 test3 = Some (V_Nat 16).
Proof. reflexivity. Qed.

Example example4 : eval_top 1000 test4 = Some (V_Nat 15).
Proof. reflexivity. Qed.

Example example5 : eval_top 1000 test5 = Some (V_Nat 14).
Proof. reflexivity. Qed.

Example example6 : eval_top 1000 myfact = Some (V_Nat 120).
Proof. reflexivity. Qed.


(** ** Άσκηση 2: Closure conversion για miniML (50 μονάδες) *)

(** Ένας πολύ συνήθης τρόπος υλοποίησης συναρτήσεων υψηλής τάξης στις
    γλώσσες προγραμματισμού είναι μέσω των closures. Οι compilers,
    μέσω ενός σταδίου που ονομάζεται closure conversion, μετατρέπουν
    τις συναρτήσεις σε closures, δηλαδή ζεύγη που αποτελούνται από τον
    κώδικα της συνάρτησης και το περιβάλλον της.

    Για να μπορεί μια συνάρτηση με ελεύθερες μεταβλητές, οι οποίες
    δεσμεύονται από εξωτερικές συναρτήσεις, να μετατραπεί σε γλώσσα
    χαμηλού επιπέδου, πρέπει να γίνει μια κλειστή συνάρτηση, δηλαδή
    χωρίς ελεύθερες μεταβλητές. Για να επιτευχθεί αυτό, το περιβάλλον
    της συνάρτησης περνιέται ως επιπλέον όρισμα, μέσω του οποίου η
    συνάρτηση μπορεί να ανακτήσει τις τιμές των ελεύθερων μεταβλητών
    της.


    Πιο συγκεκριμένα, κατά το closure conversion συμβαίνουν τα εξής:

    - Μια συνάρτηση μετατρέπεται σε ένα ζεύγος που περιλαμβάνει το
      περιβάλλον της και τον ορισμό της. Το περιβάλλον αυτό περιέχει
      τις τιμές όλων των ελεύθερων μεταβλητών σε ένα tuple.

    - Ο ορισμός μιας συνάρτησης τροποποιείται ώστε να δέχεται ως
      παράμετρο ένα ζεύγος που αποτελείται από την αρχική παράμετρο
      και το περιβάλλον της συνάρτησης. Οι τιμές των ελεύθερων
      μεταβλητών ανακτώνται από το περιβάλλον που έχει περαστεί ως
      όρισμα.

    Κατά την κλήση μιας συνάρτησης που έχει υποστεί closure
    conversion, το περιβάλλον και ο κώδικας της συνάρτησης εξάγονται
    από το closure, και η συνάρτηση εφαρμόζεται πάνω στο ζεύγος που
    περιλαμβάνει το αρχικό όρισμα και το περιβάλλον του closure.

    Τα παραπάνω περιγράφονται από τον ακόλουθο ψευδοκώδικα: *)

(**
    closure_convert (fun x -> t) = { {fv1, ... fvn},
                                     fun arg ->
                                       let x = arg # 0 in
                                       let env = arg # 1 in
                                       let fv1 = env # 0 in
                                       ...
                                       let fvn = env # (n-1) in
                                       closure_convert t }

     όπου fv1, ..., fvn οι ελεύθερες μεταβλητές της συνάρτησης.

     closure_convert (t1 t2) = let t1' = closure_convert t1 in
                               let t2' = closure_convert t2 in
                               let f_env = t1' # 0 in
                               let f_fun = t1' # 1 in
                               f_fun { t2', f_env }

   Ερώτηση: Τι μπορεί να βελτιωθεί στον παραπάνω κώδικα;
*)

(** Η άσκηση σας ζητάει να υλοποιήσετε ένα closure conversion πέρασμα
    για την MiniML. *)               


Module ClosureConversion.

  (** Σας δίνεται μία συνάρτηση που βρίσκει τις ελεύθερες μεταβλητές
      ενός όρου, δοσμένων κάποιων μεταβλητών που είναι δεσμευμένες και
      δεν πρέπει να θεωρηθούν ελεύθερες. *)

  Fixpoint free_vars_aux (bound : list string) (acc : list string) (t : term)
    : list string :=
    match t with
    | <[ t1 t2 ]> => free_vars_aux bound (free_vars_aux bound acc t2) t1
    | <[ fun x -> t ]> => free_vars_aux (x :: bound) acc t
    | T_Var x => if in_dec string_dec x bound then acc else x :: acc
    | T_Nat _ => acc
    | T_Bool _ => acc
    | T_BOp _ t1 t2 => free_vars_aux bound (free_vars_aux bound acc t2) t1
    | T_UOp _ t => free_vars_aux bound acc t
    | T_Tuple ts => fold_left (free_vars_aux bound) ts acc
    | <[ t # n ]> => free_vars_aux bound acc t
    | <[ let x := t1 in t2 ]> =>
        free_vars_aux bound (free_vars_aux (x :: bound) acc t2) t1
    | <[ if t1 then t2 else t3 ]> =>
        free_vars_aux bound (free_vars_aux bound (free_vars_aux bound acc t3) t2) t1
    end.

  Definition free_vars (bound : list string) (t : term) : list string :=
    free_vars_aux bound [] t. 
    
  (** Σημείωση 1: Μπορείτε να χρησιμοποιείτε τις ίδιες μεταβλητές για
      κάθε συνάρτηση για τα νέα ονόματα που εμφανίζονται στον κώδικα
      μετά το closure conversion. Για παράδειγμα, στον παραπάνω
      ψευδοκώδικα χρησιμοποιήσαμε τις [f_fun], [f_env], [arg], [x],
      [env]. Με αυτόν τον τρόπο, η υλοποίηση απλοποιείται, καθώς δεν
      είναι απαραίτητο να δημιουργείται νέο όνομα μεταβλητής κάθε
      φορά.

      Για να αποφευχθούν συγκρούσεις με τα ονόματα των μεταβλητών του
      αρχικού προγράμματος, θεωρούμε ότι όλες οι μεταβλητές των
      προγραμμάτων που θα χρησιμοποιηθούν ως tests ξεκινούν από κάποιο
      γράμμα. Έτσι, μπορείτε να χρησιμοποιήσετε μεταβλητές των οποίων
      τα ονόματα ξεκινούν, για παράδειγμα, με κάτω παύλα (π.χ. _f_env).

      Αυτό είναι απλώς μια σύμβαση για να απλοποιηθεί η υλοποίηση. Σε
      μια πιο ρεαλιστική υλοποίηση, θα επιλέγαμε ονόματα μεταβλητών
      που δεν χρησιμοποιούνται ήδη (fresh variable names).

      Σημείωση 2: Όταν γράφετε concrete syntax για τη miniML, δεν
      μπορείτε να καλείτε συναρτήσεις Coq (όπως στον ψευδοκώδικα),
      καθώς αυτό έρχεται σε σύγκρουση με τη σύνταξη της κλήσης
      συνάρτησης της miniML.

      closure_convert (t1 t2) = let t1' = closure_convert t1 in
                               let t2' = closure_convert t2 in
                               let f_env = t1' # 0 in
                               let f_fun = t1' # 1 in
                               f_fun { t2', f_env }
  *)


  (** Συμπληρώστε την παρακάτω συνάρτηση *)

  Definition _arg : string := "_arg".
  Definition _env : string := "_env".

  Fixpoint closure_conv (t : term) : term :=
    match t with
    | T_Lambda x t =>
      let fvs := free_vars [x] t in
      let fvs_tuple := T_Tuple (map T_Var fvs) in
      let fvs_with_idx := combine fvs (seq 0 (length fvs)) in
      let fvs_term := fold_left (
        fun t '(fvn, n) => <[ let fvn := _env # n in t ]>) fvs_with_idx (closure_conv t) in
      <[ 
        { fvs_tuple,
        fun _arg ->
          let x := _arg # 0 in
          let _env := _arg # 1 in
          fvs_term }
      ]>
    | T_App t1 t2 =>
      let t1' := closure_conv t1 in
      let t2' := closure_conv t2 in
      let f_env := <[ t1' # 0 ]> in
      let f_fun := <[ t1' # 1 ]> in
      <[ f_fun { t2', f_env } ]>
    | T_BOp bop t1 t2 => T_BOp bop (closure_conv t1) (closure_conv t2)
    | T_UOp op t => T_UOp op (closure_conv t)
    | T_Tuple ts => T_Tuple (map closure_conv ts)
    | T_Proj n t => T_Proj n (closure_conv t)
    | T_Let x t1 t2 => T_Let x (closure_conv t1) (closure_conv t2)
    | T_If t1 t2 t3 => T_If (closure_conv t1) (closure_conv t2) (closure_conv t3)
    | _ => t
    end.

  (** Εάν ο ορισμός σας είναι σωστός τα παρακάτω tests θα πρέπει να επιτυγχάνουν. *)

  Example example1 : eval_top 1000 (closure_conv test1) = Some (V_Nat 8).
  Proof. reflexivity. Qed.

  Example example2 : eval_top 1000 (closure_conv test2) = Some (V_Nat 15).
  Proof. reflexivity. Qed.

  Example example3 : eval_top 1000 (closure_conv test3) = Some (V_Nat 16).
  Proof. reflexivity. Qed.

  Example example4 : eval_top 1000 (closure_conv test4) = Some (V_Nat 15).
  Proof. reflexivity. Qed.

  Example example5 : eval_top 1000 (closure_conv test5) = Some (V_Nat 14).
  Proof. reflexivity. Qed.

  Example example6 : eval_top 1000 (closure_conv myfact) = Some (V_Nat 120).
  Proof. reflexivity. Qed.

  (** Έχοντας υλοποιήσει τα closures μέσα στην ίδια τη γλώσσα, πλέον
      μπορούμε να γράψουμε έναν interpreter που δεν χρειάζεται
      closures για τη λειτουργία του.

      Οι τιμές για το μοντέλο εκτέλεσης μετά το closure conversion δεν
      χρειάζονται closures, καθώς οι συναρτήσεις δεν έχουν ελεύθερες
      μεταβλητές.

      Το περιβάλλον περιέχει μόνο τις τιμές των παραμέτρων της
      τρέχουσας συνάρτησης και των τιμών που έχουν δεσμευτεί με
      let. *)

  Inductive value : Type :=
  (* Functions *)
  | V_Fun :
    string -> term ->
    value
  (* Natural Numbers *)
  | V_Nat : nat -> value
  (* Booleans *)
  | V_Bool : bool -> value
  (*  Tuples *)
  | V_Tuple : list value -> value. 

  Definition environment : Type := var_map value.

  (** Προσαρμόστε τον ορισμό του παραπάνω interpreter ώστε να μην χρησιμοποιεί closures. *)

  Fixpoint eval (fuel : nat) (env : environment) (t : term) : option value :=
    match fuel with
    | 0 => None
    | S fuel' =>
      match t with
      (* Application *)
      | <[ t1 t2 ]> =>
        match eval fuel' env t1 with
        (* <[ fun x -> t ] *)
        | Some (V_Fun x t) =>
          match eval fuel' env t2 with
          | Some v => eval fuel' (add x v env) t
          | None => None
          end
        (* If t1 does not evaluate to a lambda function
        then the application term is ill-formed *)
        | _ => None
        end
      (* Let *)
      | <[ let x := t1 in t2 ]> =>
        match eval fuel' env t1 with
        | Some v => eval fuel' (add x v env) t2
        | None => None
        end
      (* If *)
      | <[ if t1 then t2 else t3 ]> =>
        match eval fuel' env t1 with
        | Some (V_Bool true) => eval fuel' env t2
        | Some (V_Bool false) => eval fuel' env t3
        | _ => None
        end
      (* Bop *)
      | T_BOp bop t1 t2 =>
        match eval fuel' env t1, eval fuel' env t2 with
        | Some (V_Bool b1), Some (V_Bool b2) =>
          match bop with
          | And => Some (V_Bool (b1 && b2))
          | Or => Some (V_Bool (b1 || b2))
          | _ => None
          end
        | Some (V_Nat n1), Some (V_Nat n2) =>
          match bop with
          | Plus => Some (V_Nat (n1 + n2))
          | Minus => Some (V_Nat (n1 - n2))
          | Mult => Some (V_Nat (n1 * n2))
          | Lt => Some (V_Bool (n1 <? n2))
          | Eq => Some (V_Bool (n1 =? n2))
          | _ => None
          end
        | _, _ => None
        end
      (* UOp *)
      | T_UOp op t =>
        match eval fuel' env t with
        | Some (V_Bool b) =>
          match op with
          | Neg => Some (V_Bool (negb b))
          end
        | _ => None
        end
      (* Tuple *)
      | T_Tuple ts =>
        match map_error (eval fuel' env) ts with
        | Some vs => Some (V_Tuple vs)
        | None => None
        end
      | T_Proj n t =>
        match eval fuel' env t with
        | Some (V_Tuple vs) =>
          match nth_error vs n with
          | Some v => Some v
          | None => None
          end
        | _ => None
        end
      (* Values *)
      | <[ fun x -> t ]> => Some (V_Fun x t)
      | T_Nat n => Some (V_Nat n)
      | T_Bool b => Some (V_Bool b)
      | T_Var x => lookup x env
    end
  end.

  Definition eval_top (fuel : nat) (t : term) : option value :=
    eval fuel empty t. 

  (** Εάν ο ορισμός σας είναι σωστός τα παρακάτω tests θα πρέπει να επιτυγχάνουν. *)

  Example example1' : eval_top 1000 (closure_conv test1) = Some (V_Nat 8).
  Proof. reflexivity. Qed.

  Example example2' : eval_top 1000 (closure_conv test2) = Some (V_Nat 15).
  Proof. reflexivity. Qed.

  Example example3' : eval_top 1000 (closure_conv test3) = Some (V_Nat 16).
  Proof. reflexivity. Qed.

  Example example4' : eval_top 1000 (closure_conv test4) = Some (V_Nat 15).
  Proof. reflexivity. Qed.

  Example example5' : eval_top 1000 (closure_conv test5) = Some (V_Nat 14).
  Proof. reflexivity. Qed.

  Example example6' : eval_top 1000 (closure_conv myfact) = Some (V_Nat 120).
  Proof. reflexivity. Qed.

  (** Μετά από το στάδιο του closure conversion, όλες οι συναρτήσεις
      στο πρόγραμμα μπορούν να μεταφερθούν στην αρχή του προγράμματος,
      με αποτέλεσμα να μην υπάρχουν πλέον φωλιασμένες συναρτήσεις. Με
      αυτόν τον τρόπο, μπορούμε να μετατρέψουμε μια γλώσσα με
      συναρτήσεις υψηλής τάξης σε μια γλώσσα χαμηλότερου επιπέδου,
      χωρίς συναρτήσεις υψηλής τάξης. Αυτός είναι ένας κλασικός
      μετασχηματισμός που χρησιμοποιείται από τους compilers για την
      υλοποίηση συναρτήσεων υψηλής τάξης. *)                

End ClosureConversion.
