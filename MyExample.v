Require Import String.
Require Import Grammar.
Require Import Main.
Require Import Generator.
Open Scope string_scope.


Inductive fact : Type :=
  | num_fact : nat -> fact
  | exp_fact : exp -> fact
with term' : Type :=
  | empty_term' : term'
  | comb_term' : fact -> term' -> term'
with term : Type :=
  | comb_term : fact -> term' -> term
with exp' : Type :=
  | comb_exp' : term -> exp' -> exp'
  | empty_exp' : exp'
with exp : Type :=
  | comb_exp : term -> exp' -> exp.

(* First, we provide the types of grammar symbols 
   and their decidable equalities. *)
Module exp_Types <: SYMBOL_TYPES.
  
   Inductive terminal' :=
   | Plus | Mult | LBracket | RBracket | Num
   . 
   
   Definition terminal := terminal'.
   
   Inductive nonterminal' :=
   | E | E' | T_ | T' | F
   .
   
   Definition nonterminal := nonterminal'.
 
   Lemma t_eq_dec : forall (t t' : terminal),
	   {t = t'} + {t <> t'}.
   Proof. decide equality. Defined.
   
   Lemma nt_eq_dec : forall (nt nt' : nonterminal),
	   {nt = nt'} + {nt <> nt'}.
   Proof. decide equality. Defined.
 
   Definition showT (a : terminal) : string :=
	 match a with
	 | Plus    => "+"
	 | Mult  => "*"
	 | LBracket  => "("
	 | RBracket => ")"
	 | Num => "Num"
	 end.
 
   Definition showNT (x : nonterminal) : string :=
	 match x with
	 | E => "E"
	 | E' => "E'"
	 | T_ => "T"
	 | T' => "T'"
	 | F => "F"
	 end.
   
   (* A Num token carries a natural number -- no other token
	  carries a meaningful semantic value. *)
   Definition t_semty (a : terminal) : Type :=
	 match a with
	 | Num => nat
	 | _   => unit
	 end.
 
   Definition nt_semty (x : nonterminal) : Type :=
	 match x with
	 | E => exp
	 | E' => exp'
	 | T_ => term
   | T' => term'
   | F => fact
	 end.
 
 End exp_Types.


Module Export G <: Grammar.T.
  Module Export SymTy := exp_Types.
  Module Export Defs  := DefsFn SymTy.
End G.

Definition exp_grammar : grammar :=
  {| start := E ;
     prods := [existT action_ty
                      (E, [NT T_; NT E'])
                      (fun tup =>
                         match tup with
                         | (t, (e, _)) =>
                           comb_exp t e
                         end);
               existT action_ty
                      (E', [T Plus; NT T_; NT E'])
                      (fun tup =>
                         match tup with
                         | (_, (t, (e', _))) =>
                           comb_exp' t e'
                         end);
               existT action_ty
                      (E', [])
                      (fun tup => 
                         match tup with
                         | _ => empty_exp'
                         end);
               existT action_ty
                      (T_, [NT F; NT T'])
                      (fun tup =>
                         match tup with
                         | (f, (t', _)) =>
                           comb_term f t'
                         end);
               existT action_ty
                      (T', [T Mult; NT F; NT T'])
                      (fun tup =>
                         match tup with
                         | (_, (f, (t', _))) =>
                           comb_term' f t'
                         end);
               existT action_ty
                      (F, [T LBracket; NT E; T RBracket])
                      (fun tup =>
                         match tup with
                         | (_, (e, (_, _))) =>
                           exp_fact e
                         end);
               existT action_ty
                      (F, [T Num])
                      (fun tup =>
                         match tup with
                         | (n, _) =>
                           num_fact n
                         end)
              ]
  |}.

Definition tok (a : terminal) (v : t_semty a) : token :=
  existT _ a v.


(**
    Inductive nullable_sym (g : grammar) : symbol -> Prop :=
    | NullableSym : forall x ys f,
        In (existT _ (x, ys) f) g.(prods)
        -> nullable_gamma g  
        -> nullable_sym g (NT x)
(* Note, this means, if we want to write an empty production, we need to explicitly state it as going to empty set [] *)
(* Specification of nullable_grammar *)
    with nullable_gamma (g : grammar) : list symbol -> Prop :=
         | NullableNil  : nullable_gamma g [] (* rhs is blank, that's empty *)
         | NullableCons : forall hd: symbol tl: [symbol],
             nullable_sym g hd
             -> nullable_gamma g tl
             -> nullable_gamma g (hd :: tl).
**)

Theorem E'_is_nullable : forall (g: grammar) (t: terminal), nullable_sym g (NT E').
Proof. 
  intros.
  apply NullableSym with (ys := []) (f := (fun tup => match tup with | _ => empty_exp' end)).
  - simpl. repeat (try apply in_eq; try apply in_cons). (* This will navigate through the list until we find our production *)
  - apply NullableNil.
Qed.


 

 

 
 
 
 
 
 
 