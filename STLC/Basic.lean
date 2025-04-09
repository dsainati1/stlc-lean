
-- de-brujin syntax for the simply typed lambda calculus with numbers, bools and pairs

inductive type : Type where
  | TNat
  | TBool
  | Mult (τ1 τ2 : type)
  | Arr (τ1 τ2 : type)

open type

@[reducible]
def context : Type := List type

inductive term : Type where
  -- basic λ calculus terms
  | Var (i : Nat)
  | Abs (τ : type) (e : term)
  | App (e1 e2 : term)

  -- numbers
  | Zro
  | Succ (e : term)
  | IsZero (e : term)

  -- bools
  | Fls
  | Tru
  | If (e1 e2 e3 : term)

  -- pairs
  | Pair (e1 e2 : term)
  | Fst (e1 : term)
  | Snd (e1 : term)

open term
open List

inductive wt : context -> term -> type -> Prop where
  | T_Var Γ i τ :
    Γ[i]? = some τ ->
    --------------------------------
    wt Γ (Var i) τ

  | T_Abs Γ τ1 τ2 e :
    wt (τ1 :: Γ) e τ2 ->
    --------------------------------
    wt Γ (Abs τ1 e) (Arr τ1 τ2)

  | T_App Γ τ1 τ2 e1 e2 :
    wt Γ e1 (Arr τ1 τ2) ->
    wt Γ e2 τ1 ->
    --------------------------------
    wt Γ (App e1 e2) τ2

  | T_Zero Γ : wt Γ Zro TNat

  | T_Succ Γ e :
    wt Γ e TNat ->
    --------------------------------
    wt Γ (Succ e) TNat

  | T_IsZero Γ e :
    wt Γ e TNat ->
    --------------------------------
    wt Γ (IsZero e) TBool

  | T_True Γ : wt Γ Tru TBool

  | T_Fls Γ : wt Γ Tru TBool

  | T_If Γ e1 e2 e3 τ :
    wt Γ e1 TBool ->
    wt Γ e2 τ ->
    wt Γ e3 τ ->
    --------------------------------
    wt Γ (If e1 e2 e3) τ

  | T_Pair Γ e1 e2 τ1 τ2 :
    wt Γ e1 τ1 ->
    wt Γ e2 τ2 ->
    --------------------------------
    wt Γ (Pair e1 e2) (Mult τ1 τ2)

  | T_Fst Γ e1 τ1 τ2 :
    wt Γ e1 (Mult τ1 τ2) ->
    --------------------------------
    wt Γ (Fst e) τ1

  | T_Snd Γ e1 τ1 τ2 :
    wt Γ e1 (Mult τ1 τ2) ->
    --------------------------------
    wt Γ (Snd e) τ1

open wt

notation Γ "⊢" e ":" τ => wt Γ e τ

def up_term (e : term) (below : Nat) : term :=
  match e with
  | Var i => if i < below then Var i else Var (i + 1)
  | Abs τ e => Abs τ (up_term e (below + 1) )
  | App e1 e2 => App (up_term e1 below) (up_term e2 below)
  | Zro => Zro
  | Succ e => Succ (up_term e below)
  | IsZero e => IsZero (up_term e below)
  | Fls => Fls
  | Tru => Tru
  | If e1 e2 e3 => If (up_term e1 below) (up_term e2 below) (up_term e3 below)
  | Pair e1 e2 => Pair (up_term e1 below) (up_term e2 below)
  | Fst e => Fst (up_term e below)
  | Snd e => Snd (up_term e below)

def subst (e : term) (var : Nat) (e' : term) : term :=
  match e with
  | Var i => if i == var then e' else e
  | Abs τ e => Abs τ (subst e (var + 1) (up_term e' 0) )
  | App e1 e2 => App (subst e1 var e') (subst e2 var e')
  | Zro => Zro
  | Succ e => Succ (subst e var e')
  | IsZero e => IsZero (subst e var e')
  | Fls => Fls
  | Tru => Tru
  | If e1 e2 e3 => If (subst e1 var e') (subst e2 var e') (subst e3 var e')
  | Pair e1 e2 => Pair (subst e1 var e') (subst e2 var e')
  | Fst e => Fst (subst e var e')
  | Snd e => Snd (subst e var e')

notation e "[" e' "]" => subst e 0 e'

def is_value (e : term) : Prop :=
  match e with
  | Zro => true
  | Tru => true
  | Fls => true
  | Var _ => true
  | Abs _ _ => true
  | IsZero _ => false
  | If _ _ _ => false
  | Fst _ => false
  | Snd _ => false
  | App _ _ => false
  | Succ e => is_value e
  | Pair e1 e2 => is_value e1 /\ is_value e2

inductive step : term -> term -> Prop where
  | E_App1 e1 e1' e2 :
      step e1 e1' ->
    --------------------------------
      step (App e1 e2) (App e1' e2)

  | E_App2 v e2' e2 :
    is_value v ->
    step e2 e2' ->
  --------------------------------
    step (App v e2) (App v e2')

  | E_AppAbs τ e v :
    is_value v ->
  --------------------------------
    step (App (Abs τ e) v) (e[v])

  | E_Succ e e' :
      step e e' ->
    --------------------------------
      step (Succ e) (Succ e')

  | E_IsZero e e' :
      step e e' ->
    --------------------------------
      step (IsZero e) (IsZero e')

  | E_IsZeroTrue :
    --------------------------------
      step (IsZero Zro) Tru

  | E_IsZeroFalse v :
      is_value v ->
    --------------------------------
      step (IsZero (Succ v)) Fls

  | E_If e1 e1' e2 e3 :
      step e1 e1' ->
    --------------------------------
      step (If e1 e2 e3) (If e1' e2 e3)

  | E_IfTrue e2 e3 :
    --------------------------------
      step (If Tru e2 e3) e2

  | E_IfFalse e2 e3 :
    --------------------------------
      step (If Fls e2 e3) e3

  | E_Pair1 e1 e1' e2 :
      step e1 e1' ->
    --------------------------------
      step (Pair e1 e2) (Pair e1' e2)

  | E_Pair2 v e2' e2 :
    is_value v ->
    step e2 e2' ->
  --------------------------------
    step (Pair v e2) (Pair v e2')

  | E_Fst e e' :
      step e e' ->
    --------------------------------
      step (Fst e) (Fst e')

  | E_FstPair v1 v2 :
      is_value v1 ->
      is_value v2 ->
    --------------------------------
      step (Fst (Pair v1 v2)) v1

  | E_Snd e e' :
      step e e' ->
    --------------------------------
      step (Snd e) (Snd e')

  | E_SndPair v1 v2 :
      is_value v1 ->
      is_value v2 ->
    --------------------------------
      step (Snd (Pair v1 v2)) v2

notation e ">->" e' => step e e'

open step

inductive multistep : term -> term -> Prop where
  | M_refl e : multistep e e
  | M_one e1 e2 e3 :
      (e1 >-> e2) ->
      multistep e2 e3 ->
      multistep e1 e3

notation e ">->*" e' => multistep e e'

open multistep

theorem normalizing : forall Γ e τ,
  (Γ ⊢ e : τ) ->
  exists e', (e >->* e') /\ is_value e' := by
  sorry
