(* Syntax of GV Terms and Types *) 

(* Add LoadPath "~/session/dblib/src". *)
Require Import List.
Require Import EqNat.
Require Import Dblib.DblibTactics.
Require Import Dblib.DeBruijn.

(* Require Import DblibTactics.
Require Import Debruijn *)

Notation "[ ]" := nil : list_scope.
Notation "[ x ]" := (cons x nil) : list_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Inductive value : Type :=
|VUnit : value | VName :> nat -> value.

Inductive type : Set :=
| TSession :> stype -> type
| T1Nul : type
| TProd : type -> type -> type
| T0Nul : type
| TSum : type -> type -> type
| TLoli : type -> type -> type
| TSharp : stype -> type
with stype : Set :=
|TSendEnd : stype
|TRecvEnd : stype
|TSend : type -> stype -> stype
|TRecv : type -> stype -> stype.
(* |TSharp : stype.*)
            (*
with ltype : Prop :=
| lAllow : type -> type -> ltype.
             *)

Definition env := list (option type).
Definition emptyEnv: env := [].

Fixpoint emptyEnvQ(e:env):bool :=
  match e with
  | [] => true
  | (Some _ :: _) => false
  | (None :: xs) => emptyEnvQ xs
  end.

(* Environmental sanity check *)
Example emptyEnv1: emptyEnvQ [] = true.
Proof. reflexivity. Qed.
Example emptyEnv2: emptyEnvQ [Some T1Nul] = false.
Proof. reflexivity. Qed.

 Fixpoint dual(s:stype):stype:=
  match s with
  | TSendEnd => TRecvEnd
  |TRecvEnd => TSendEnd
  |(TSend T s) => TRecv T (dual s)
  |(TRecv T s) => TSend T (dual s)
  end.

(* Inductive term: env -> type -> env -> Prop :=
| E1Nul: forall g, term g T1Nul g
| EVar : forall g t s, t <> (TSession s) -> term g t g
(* | EPair : forall g g' g'', term g M g -> term g' N g' -> term (res g g') (TProd M N) (res g g') *)
| EInl : forall g t u, term g t g -> term g (TSum t u) g
| EInr : forall g t u, term g u g -> term g (TSum t u) g.
 *)

 Inductive constant : Type :=
 | send : constant
 | receive : constant
 | fork : constant
 | wait : constant
 | link : constant.

(* GV Constants *)
(*Inductive constant :=
  | send : forall S T, TLoli (TProd T (TSend T S)) S -> constant.
Definition receive{S : stype}{T : type} := TLoli (TRecv T S) (TProd T S).
Definition fork{S : stype} := TLoli (TLoli S TSendEnd) (dual S).
Definition wait:= TLoli TRecvEnd T1Nul.
Definition link{S : stype} := TLoli (TProd S (dual S)) TSendEnd.
*)

Inductive term : Set :=
| EVar : nat -> term
| ECApp : constant -> term -> term
| ELam : term -> term
| EApp : term -> term -> term
| EPair : term -> term -> term
| ELetPair : term -> term -> term -> term
| EInl : term -> term
| EInr : term -> term
| ECase : term -> term -> term -> term
| EUnit : term
| ELetUnit : term -> term -> term
| EAbsurd : term -> term.

Instance Var_term : Var term := {
  var := EVar
                               }.

Fixpoint traverse_term (f : nat -> nat -> term) l t :=
  match t with
  | EVar x => f l x
  | ECApp c t => ECApp c (traverse_term f l t)
  | ELam t => ELam (traverse_term f (1+l) t)
  | EApp t1 t2 => EApp (traverse_term f l t1) (traverse_term f l t2)
  | EPair t1 t2 => EPair (traverse_term f l t1) (traverse_term f l t2)
  | ELetPair t t2 t3 => ELetPair (traverse_term f l t) (traverse_term f l t2) (traverse_term f l t3)
  | EInl t => EInl (traverse_term f l t)
  | EInr t => EInr (traverse_term f l t)
  | ECase t t1 t2 => ECase (traverse_term f l t) (traverse_term f l t1) (traverse_term f l t2)
  | EUnit => EUnit
  | ELetUnit M N => ELetUnit (traverse_term f l M) (traverse_term f l N)
  | EAbsurd M => EAbsurd (traverse_term f l M)
  end.

Instance Traverse_term : Traverse term term := {
                                                traverse := traverse_term
                                              }.

Instance TraverseVarInjective_term : @TraverseVarInjective term _ term _.
Proof. constructor. prove_traverse_var_injective. Qed.

Instance TraverseFunctorial_term : @TraverseFunctorial term _ term _.
Proof. constructor. prove_traverse_functorial. Qed.

Instance TraverseRelative_term : @TraverseRelative term term _.
Proof. constructor. prove_traverse_relative. Qed.

Instance TraverseIdentifiesVar_term : @TraverseIdentifiesVar term _ _.
Proof. constructor. prove_traverse_identifies_var. Qed.

Instance TraverseVarIsIdentity_term : @TraverseVarIsIdentity term _ term _.
Proof. constructor. prove_traverse_var_is_identity. Qed.

(*
Inductive type_check : env -> term -> type -> Prop :=
  (*  | type_Val : forall t, (type_check (EVal) t). *)
| type_var : forall (g : env)(e:term)(t:type)(s : stype), t <> (TSharp s) -> type_check g e t.
(* | type_fun : forall (g : env)(e : term)(t:type), *)
*)

Notation "! T . S" := (TSend T S) (at level 20).
Notation "? T . S" := (TRecv T S) (at level 20).
Notation "end!" := TSendEnd.
Notation "end?" := TRecvEnd. 

Lemma dual_inverse : forall s, dual (dual s) = s.
Proof. induction s; simpl.
       - reflexivity.
       - reflexivity.
       - rewrite IHs. reflexivity.
       - rewrite IHs. reflexivity.
Qed.

(*  *)

