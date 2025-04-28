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

  | T_Tru Γ : wt Γ Tru TBool

  | T_Fls Γ : wt Γ Fls TBool

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

  | T_Fst Γ e τ1 τ2 :
    wt Γ e (Mult τ1 τ2) ->
    --------------------------------
    wt Γ (Fst e) τ1

  | T_Snd Γ e τ1 τ2 :
    wt Γ e (Mult τ1 τ2) ->
    --------------------------------
    wt Γ (Snd e) τ2

open wt

notation Γ "⊢" e ":" τ => wt Γ e τ

@[simp]
def up_term (e : term) (above : Nat) : term :=
  match e with
  | Var i => if i <= above then Var (i + 1) else Var i
  | Abs τ e => Abs τ (up_term e (above + 1) )
  | App e1 e2 => App (up_term e1 above) (up_term e2 above)
  | Zro => Zro
  | Succ e => Succ (up_term e above)
  | IsZero e => IsZero (up_term e above)
  | Fls => Fls
  | Tru => Tru
  | If e1 e2 e3 => If (up_term e1 above) (up_term e2 above) (up_term e3 above)
  | Pair e1 e2 => Pair (up_term e1 above) (up_term e2 above)
  | Fst e => Fst (up_term e above)
  | Snd e => Snd (up_term e above)


@[simp]
def subst (e : term) (var : Nat) (e' : term) : term :=
  match e with
  | Var i =>
    if i == var then e' else
    if i > var then Var (i - 1) else Var i
  | Abs τ e => Abs τ (subst e (var + 1) e' )
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

notation e "[" e' " at" k "]" => subst e k e'
notation e "[" e' "]" => e[e' at 0]

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

theorem value_does_not_step e :
  is_value e ->
  ¬ (exists e', e >-> e') := by

  intros h contra
  induction e
  all_goals (try contradiction)
  all_goals (try cases contra; contradiction)
  . case Succ e IH =>
    let ⟨e', Hstep⟩ := contra
    unfold is_value at h
    apply IH h
    cases Hstep
    . case E_Succ e'' Hstep =>
      exists e''
  . case Pair e1 e2 IH1 IH2 =>
    unfold is_value at h
    let ⟨h1, h2⟩ := h; clear h
    specialize IH1 h1
    specialize IH2 h2
    let ⟨e', Hstep⟩ := contra
    cases Hstep
    . case E_Pair1 e1' Hstep =>
      apply IH1
      exists e1'
    . case E_Pair2 e2' HValue Hstep =>
      apply IH2
      exists e2'

inductive multistep : term -> term -> Prop where
  | M_refl e : multistep e e
  | M_one e1 e2 e3 :
      (e1 >-> e2) ->
      multistep e2 e3 ->
      multistep e1 e3

notation e ">->*" e' => multistep e e'

open multistep

theorem multistep_comp e1 e2 e3 :
  (e1 >->* e2) ->
  (e2 >->* e3) ->
  e1 >->* e3 := by

  intros H1 H2
  induction H1
  . case M_refl e1' =>
    induction H2
    . case M_refl e2' =>
      constructor
    . case M_one e1'' e2'' e3'' IH =>
      apply M_one
      all_goals trivial
  . case M_one e1'' e2'' e3'' IH =>
    apply M_one
    all_goals (try trivial)
    apply IH
    trivial

theorem multistep_congr_succ e1 e2 :
  (e1 >->* e2) ->
  (Succ e1 >->* Succ e2) := by

  intros H
  induction H
  . constructor
  . case M_one e1 e2 e3 Hone Hrest IH =>
    apply M_one
    all_goals (try trivial)
    constructor
    trivial

theorem multistep_congr_isZero e1 e2 :
  (e1 >->* e2) ->
  (IsZero e1 >->* IsZero e2) := by

  intros H
  induction H
  . constructor
  . case M_one e1 e2 e3 Hone Hrest IH =>
    apply M_one
    all_goals (try trivial)
    constructor
    trivial

theorem multistep_congr_fst e1 e2 :
  (e1 >->* e2) ->
  (Fst e1 >->* Fst e2) := by

  intros H
  induction H
  . constructor
  . case M_one e1 e2 e3 Hone Hrest IH =>
    apply M_one
    all_goals (try trivial)
    constructor
    trivial

theorem multistep_congr_snd e1 e2 :
  (e1 >->* e2) ->
  (Snd e1 >->* Snd e2) := by

  intros H
  induction H
  . constructor
  . case M_one e1 e2 e3 Hone Hrest IH =>
    apply M_one
    all_goals (try trivial)
    constructor
    trivial

theorem multistep_congr_if e1 e1' e2 e3 :
  (e1 >->* e1') ->
  (If e1 e2 e3 >->* If e1' e2 e3) := by

  intros H
  induction H
  . constructor
  . case M_one e1 e2 e3 Hone Hrest IH =>
    apply M_one
    all_goals (try trivial)
    constructor
    trivial

theorem multistep_congr_pair e1 e1' e2 e2' :
  (e1 >->* e1') ->
  is_value e1' ->
  (e2 >->* e2') ->
  (Pair e1 e2 >->* Pair e1' e2') := by

  intros H1 Hval H2
  induction H1
  . case M_refl e1' =>
    induction H2
    . case M_refl e2' =>
      constructor
    . case M_one =>
      apply M_one
      apply E_Pair2
      all_goals trivial
  . case M_one e1' e1'' e1'' _ _ IH =>
    apply M_one
    apply E_Pair1
    all_goals (try trivial)
    apply IH
    trivial

theorem multistep_congr_app e1 e1' e2 e2' :
  (e1 >->* e1') ->
  is_value e1' ->
  (e2 >->* e2') ->
  (App e1 e2 >->* App e1' e2') := by

  intros H1 Hval H2
  induction H1
  . case M_refl e1' =>
    induction H2
    . case M_refl e2' =>
      constructor
    . case M_one =>
      apply M_one
      apply E_App2
      all_goals try trivial
  . case M_one e1' e1'' e1'' _ _ IH =>
    apply M_one
    apply E_App1
    all_goals (try trivial)
    apply IH
    trivial
