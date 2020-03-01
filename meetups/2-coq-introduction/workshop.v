Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Print negb.

(* 'Compute' command evaluates the expression  *)
Compute negb true.

(*'Check' command shows the type of the expression*)
Check negb.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Compute orb true false.

Check orb.

(* Currying:
   A -> B -> C is morally equivalent to 
   (A, B) -> C
*)

Check orb true.
Check orb true true.


(* Proving simple facts *)
Theorem test_andb: (andb true true) = true.
Proof. (* Enter the proof mode *)
  simpl.  (* Tactic: try to simplify the expression *)
  reflexivity. (* Tactic: proofs things like 'A = A' *)
Qed.

Theorem test_orb: (andb (orb true false) false) = false.
Proof.
  simpl. 
  reflexivity.
Qed.


(* Prove a statement for all booleans *)
Theorem and_true: forall b: bool, (andb b true) = b.
Proof.
  intros. (* Tactic: introduce a variable *)
  
  (* Above the line: assumptions
     Below the line: goal(s)
   *)
  simpl. (* Simplification does nothing :( *)
  destruct b. (* Tactic: perform case analysis *)
  - simpl. reflexivity. (* Case: b = true *)
  - simpl. reflexivity. (* Case b = false *)   
Qed.

(* Prove the same fact shorter *)
Theorem and_true_again: forall b: bool, (andb b true) = b.
Proof.
  intros.
  destruct b.
  - auto. (* Tactic: automatically find a proof (works for trivial facts) *)
  - auto.
Qed.

(* Excercise *)
Theorem or_commutes: forall a b, (orb a b) = (orb b a).
Proof. 
  Admitted.



(* Natural numbers *)

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Check O.
Check S O. (* Represents '1' *)
Check S (S O). (* Represents '2' *)
Check S (S (S O)). (* Represents '3' *)

End NatPlayground.


(* Now we use 'nat' from the standard library *)
Check (S (S (S (S O)))).  (* It pretty-prints natural numbers*)

(* Data constructors are available as functions *)
Check O. (* nat *)
Check S. (* nat -> nat *)


Module NatPlayground2.

(* Declare a recursive function *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.


(* Recursion has to be proven to terminate *)


(* Fixpoint bad (n : nat) : nat := 
  match n with
  | 0 => 0
  | S n' => bad (S (S (n')))
  end. *)

End NatPlayground2.


(* Encoding properties *)

Inductive even : nat -> Prop := 
| z_even : even 0
| plus2_even : forall (n : nat), (even n) -> even (S (S n)).


Check even 3.  (* Proposition *)
Check even. (* Not a proposition itself. Predicate *)
Check z_even.
Check plus2_even.
Check plus2_even 4.

(* Curry-Howard correspondence: *)
(* To prove that 2 is even - construct an object of type 'even 2' *)

(* Proof object for proposition 'even 2'*)
Check plus2_even 0 z_even. (* Proof object for proposition 'even 2'*)

(* Proof object for proposition 'even 4'*)
Check plus2_even 2 (plus2_even 0 z_even).


(* Manually constructing proof objects is hard
  Try tactics
 *)
Theorem eight_is_even: even 8.
Proof.
  apply plus2_even.
  apply plus2_even.
  apply plus2_even.
  apply plus2_even.
  apply z_even.
Qed.

Print eight_is_even. (* <- a proof is just an object! *)
  
Theorem eight_is_even_shorter: even 8.
Proof.
  constructor. 
 (* Tactic: find a constructor matching the goal *)
  constructor.
  constructor.
  constructor.
  constructor.
Qed.


(* Proving negative statements *)

Theorem five_not_even: not (even 5).
Proof.
  unfold not.
  (* Curry-Howard: to prove A construct (A -> False) object *)
  intros.
  inversion H. (* Tactic: find how an object could be constructed*)
  subst.
  inversion H1. subst.
  inversion H2.
Qed.

(* What is False? - A type without constructors *)
Print False.
Check False.


(* Proof by induction (Slides)*)

Theorem plus0: forall n, n + 0 = n.
Proof.
  induction n.
  - auto.
  - simpl.
    f_equal. (* Tactic:  if x = y then f(x) = f(y) *)
    apply IHn. 
Qed.

Theorem a_plus_sb: forall a b, (a + (S b)) = S (a + b).
Proof.
  induction a.
  -  simpl. auto. 
  - intros. simpl. f_equal. apply IHa.
Qed. 

Theorem plus_comm: forall a b, (a + b) = (b + a).
Proof.
  Admitted.


(* Structural induction *)

Fixpoint add (n : nat) (m : nat) : nat :=
  match n with
    | O => m (* Looks like induction base case *)
    | S n' => S (add n' m) (* Looks like induction step *)
  end.

(* Induction: allow to use the proof for subexpression 
   to build a proof for the expression *)



Inductive tree: Type :=
  | empty 
  | branch (l: tree)  (v: nat)  (r: tree)
  .

Require Import Nat.

(* Insert new number into a search tree *)
Fixpoint insert (n: nat) (t: tree): tree :=
  match t with 
  | empty => branch empty n empty
  | branch l v r => if (leb n v) 
                    (* recursive call on the left branch*)
                    then branch (insert n l) v r
                    (* recursive call on the right branch*)
                    else branch l v (insert n r)
  end.

(* Property: 'number is present in the tree' *)
Inductive In: nat -> tree -> Prop :=
 | in_root : forall l r n, In n (branch l n r)
 | in_left : forall l v r n, (In n l) ->  In n (branch l v r)
 | in_right : forall l v r n, (In n r) ->  In n (branch l v r)
.

Theorem contains_after_insert: forall n t, In n (insert n t).
Proof.
  induction t.  (* t is a tree but still supports induction *)
  -  simpl. constructor. (* base case*)
  -  simpl. (* See IHn1 and IHn2 *)
     destruct (leb n v) eqn: e.
     -- apply in_left.
        apply IHt1. (* Apply induction hypothesysis for the left subtree *)
     -- apply in_right.
        apply IHt2. (* Apply induction hypothesysis for the right subtree *)
Qed.

(* How induction works under ther hood: 
   Coq generates 'Datatype_ind' function for 
   every inductive Datatype
*)

Check nat_ind.
Check tree_ind.

Print contains_after_insert. (* <- uses tree_ind *)

Check bool_ind.

Inductive natlist : Type :=
    | nnil : natlist 
    | ncons  (head: nat) (tail : natlist).

Check natlist_ind.


(* ===== Was not presented due to lack of time ======= *)


Inductive sorted: list nat -> Prop :=
| sorted_nil:
    sorted nil
| sorted_1: forall x,
    sorted (x::nil)
| sorted_cons: forall x y l,
   le x y -> sorted (y::l) -> sorted (x::y::l).

Inductive Permutation {A : Type} : list A -> list A -> Prop :=
    perm_nil : Permutation nil nil 
  | perm_skip : forall (x : A) (l l' : list A),
                Permutation l l' ->
                Permutation (x :: l) (x :: l')
  | perm_swap : forall (x y : A) (l : list A),
                Permutation (y :: x :: l) (x :: y :: l)
  | perm_trans : forall l l' l'' : list A,
                 Permutation l l' ->
                 Permutation l' l'' ->
                 Permutation l l''.

Definition is_a_sorting_algorithm (f: list nat -> list nat) :=
  forall input, and (Permutation input (f input)) (sorted (f input)).

Fixpoint alg (l : list nat): list nat := 
   nil.

Theorem my_alg_is_correct: is_a_sorting_algorithm alg.
Proof. 
Admitted.





