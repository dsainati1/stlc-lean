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

inductive multistep : term -> term -> Prop where
  | M_refl e : multistep e e
  | M_one e1 e2 e3 :
      (e1 >-> e2) ->
      multistep e2 e3 ->
      multistep e1 e3

notation e ">->*" e' => multistep e e'

open multistep

theorem canonical_forms_bool v :
  ([] ⊢ v : TBool) ->
  is_value v ->
  v = Tru \/ v = Fls := by

  intros Hwt Hv
  cases Hwt
  all_goals (try contradiction)
  . left
    rfl
  . right
    rfl

theorem canonical_forms_nat v :
  ([] ⊢ v : TNat) ->
  is_value v ->
  v = Zro \/ (exists v', v = Succ v' /\ is_value v'):= by

  intros Hwt Hv
  cases Hwt with
  | T_Zero =>
      left
      rfl
  | T_Succ Γ e Hwt =>
      right
      exists e
  | _ => contradiction

theorem canonical_forms_fun τ1 τ2 v :
  ([] ⊢ v : (Arr τ1 τ2)) ->
  is_value v ->
  exists e, v = Abs τ1 e := by

  intros Hwt Hv
  cases Hwt with
  | T_Abs Γ τ1 τ2 e Hwt => exists e
  | _ => contradiction

theorem canonical_forms_pair τ1 τ2 v :
  ([] ⊢ v : (Mult τ1 τ2)) ->
  is_value v ->
  exists v1 v2, v = Pair v1 v2 /\ is_value v1 /\ is_value v2 := by

  intros Hwt Hv
  cases Hwt with
  | T_Pair Γ e1 e2 τ1 τ2 Hwt1 Hwt2 =>
    exists e1
    exists e2
  | _ => contradiction

theorem progress : forall e τ,
  ([] ⊢ e : τ) ->
  is_value e \/ exists e', e >-> e' := by

  intros e τ HWt
  generalize hΓ : [] = Γ
  rw [hΓ] at HWt
  induction HWt with
  | T_Var Γ i τ Hi =>
    rw [<-hΓ] at Hi
    contradiction
  | T_Abs Γ' τ1 τ2 e HWt IH =>
    left
    trivial
  | T_App Γ' τ1 τ2 e1 e2 Hwt1 Hwt2 IH1 IH2 =>
    right
    rw [<-hΓ] at Hwt1
    rw [<-hΓ] at Hwt2
    specialize IH1 hΓ
    specialize IH2 hΓ
    cases IH1
    . case inl IH1 =>
      cases IH2
      . case inl IH2 =>
        have hFun := canonical_forms_fun τ1 τ2 e1 Hwt1 IH1
        let ⟨e, he⟩ := hFun
        rw [he]
        exists e[e2]
        apply E_AppAbs
        trivial
      . case inr IH2 =>
        let ⟨e, he⟩ := IH2
        exists (App e1 e)
        apply E_App2
        trivial
        trivial
    . case inr IH1 =>
        let ⟨e, he⟩ := IH1
        exists (App e e2)
        apply E_App1
        trivial
  | T_Zero Γ =>
      left
      trivial
  | T_Succ Γ' e' Hwt IH =>
      specialize IH hΓ
      cases IH
      . case inl IH =>
        left
        trivial
      . case inr IH =>
        let ⟨e, he⟩ := IH
        right
        exists (Succ e)
        apply E_Succ
        trivial
  | T_IsZero Γ' e' Hwt IH =>
      specialize IH hΓ
      rw [<-hΓ] at Hwt
      right
      cases IH
      . case inl IH =>
        have hNat := canonical_forms_nat e' Hwt IH
        cases hNat
        . case inl h =>
          exists Tru
          rw [h]
          apply E_IsZeroTrue
        . case inr h =>
          exists Fls
          let ⟨v, hsucc, hvalue⟩ := h
          rw [hsucc]
          apply E_IsZeroFalse
          trivial
      . case inr IH =>
        let ⟨e'', he'⟩ := IH
        exists (IsZero e'')
        apply E_IsZero
        trivial
  | T_Tru Γ' =>
    left
    trivial
  | T_Fls Γ' =>
    left
    trivial
  | T_If Γ' e1 e2 e3 τ' Hwt1 Hwt2 Hwt3 IH1 IH2 IH3 =>
    right
    specialize IH1 hΓ
    specialize IH2 hΓ
    specialize IH3 hΓ
    rw [<-hΓ] at Hwt1
    cases IH1
    . case inl IH1 =>
      have hBool := canonical_forms_bool e1 Hwt1 IH1
      cases hBool
      . case inl hBool =>
        rw [hBool]
        exists e2
        constructor
      . case inr hBool =>
        rw [hBool]
        exists e3
        constructor
    . case inr IH1 =>
      let ⟨e1', he1⟩ := IH1
      exists (If e1' e2 e3)
      constructor
      trivial
  | T_Pair Γ' e1 e2 τ1 τ2 Hwt1 Hwt2 IH1 IH2 =>
    specialize IH1 hΓ
    specialize IH2 hΓ
    cases IH1
    . case inl IH1 =>
      cases IH2
      . case inl IH2 =>
        left
        trivial
      . case inr IH2 =>
        right
        let ⟨e2', he2⟩ := IH2
        exists (Pair e1 e2')
        constructor
        trivial
        trivial
    . case inr IH1 =>
      let ⟨e1', he1⟩ := IH1
      right
      exists (Pair e1' e2)
      constructor
      trivial
  | T_Fst Γ' e' τ1 τ2 Hwt IH =>
    right
    specialize IH hΓ
    rw [<-hΓ] at Hwt
    cases IH
    . case inl IH =>
      have hPair := canonical_forms_pair τ1 τ2 e' Hwt IH
      let ⟨v1, v2, He, Hv1, Hv2⟩ := hPair
      rw [He]
      exists v1
      constructor
      trivial
      trivial
    . case inr IH =>
      let ⟨e', he⟩ := IH
      exists (Fst e')
      constructor
      trivial
  | T_Snd Γ' e' τ1 τ2 Hwt IH =>
    right
    specialize IH hΓ
    rw [<-hΓ] at Hwt
    cases IH
    . case inl IH =>
      have hPair := canonical_forms_pair τ1 τ2 e' Hwt IH
      let ⟨v1, v2, He, Hv1, Hv2⟩ := hPair
      rw [He]
      exists v2
      constructor
      trivial
      trivial
    . case inr IH =>
      let ⟨e', he⟩ := IH
      exists (Snd e')
      constructor
      trivial

theorem weakening : forall Γ Γ' e τ,
  (Γ' ⊢ e : τ) ->
  List.IsPrefix Γ' Γ  ->
  Γ ⊢ e : τ := by

  intro Γ Γ' e τ Hwt Hpre
  revert Γ
  induction Hwt with
  | T_Var Γ'' i τ' HΓ =>
      intros Γ Hpre
      let ⟨post, Hpost⟩ := Hpre
      rw [<-Hpost]
      constructor
      rw [<-HΓ]
      apply List.getElem?_append_left
      have hsome : Γ''[i]?.isSome = true := by simp [HΓ]
      rw [isSome_getElem?] at hsome
      trivial
  | T_Abs Γ'' τ1 τ2 e' Hwt' IH =>
    intros Γ Hpre
    let ⟨post, Hpost⟩ := Hpre
    rw [<-Hpost]
    constructor
    simp [IH]
  | T_App Γ' τ1 τ2 e1 e2 Hwt1 Hwt2 IH1 IH2 =>
    intros Γ Hpre
    let ⟨post, Hpost⟩ := Hpre
    rw [<-Hpost]
    constructor
    . apply IH1
      simp
    . apply IH2
      simp
  | T_Zero Γ =>
    intros Γ Hpre
    constructor
  | T_Succ Γ' e' Hwt IH =>
    intros Γ Hpre
    constructor
    apply IH
    trivial
  | T_IsZero Γ' e' Hwt IH =>
    intros Γ Hpre
    constructor
    apply IH
    trivial
  | T_Tru Γ' =>
    intros Γ Hpre
    constructor
  | T_Fls Γ' =>
    intros Γ Hpre
    constructor
  | T_If Γ' e1 e2 e3 τ' Hwt1 Hwt2 Hwt3 IH1 IH2 IH3 =>
    intros Γ Hpre
    constructor
    . apply IH1
      trivial
    . apply IH2
      trivial
    . apply IH3
      trivial
  | T_Pair Γ' e1 e2 τ1 τ2 Hwt1 Hwt2 IH1 IH2 =>
    intros Γ Hpre
    constructor
    . apply IH1
      trivial
    . apply IH2
      trivial
  | T_Fst Γ' e' τ1 τ2 Hwt IH =>
    intros Γ Hpre
    constructor
    apply IH
    trivial
  | T_Snd Γ' e' τ1 τ2 Hwt IH =>
    intros Γ Hpre
    constructor
    apply IH
    trivial

theorem weaken_empty : forall Γ e τ,
  ([] ⊢ e : τ) ->
  Γ ⊢ e : τ := by
  intros
  apply weakening
  all_goals (try trivial)
  simp

theorem subst_pres_typing : forall Γ Γ' e v τ τ',
  ((Γ' ++ (τ' :: Γ)) ⊢ e : τ) ->
  ([] ⊢ v : τ') ->
  (Γ' ++ Γ) ⊢ (e[v at (List.length Γ')]) : τ := by

  intro Γ Γ' e
  revert Γ Γ'
  induction e with
  | Var i =>
    intro Γ Γ' v τ τ' Hwt Hvwt
    simp
    by_cases (i = List.length Γ')
    . case pos h =>
      simp [h]
      . cases Hwt
        . case T_Var H =>
          rw [List.getElem?_append_right] at H
          . simp [h] at H
            subst H
            apply weaken_empty
            trivial
          . simp [h]
    . case neg h =>
      simp [h]
      cases Hwt
      . case T_Var H =>
        by_cases (List.length Γ' < i)
        . case pos h2 =>
          simp [h2]
          constructor
          rw [List.getElem?_append_right, List.getElem?_cons] at H
          rw [<-H]
          have h3 : ¬(i - List.length Γ' = 0) := by omega
          simp [h3]
          rw [List.getElem?_append_right]
          congr 1
          all_goals omega
        . case neg h2 =>
          simp [h2]
          constructor
          rw [List.getElem?_append_left] at H
          rw [List.getElem?_append_left]
          trivial
          omega
          omega
  | Abs τ1 e' IH =>
    intro Γ Γ' v τ τ' Hwt Hvwt
    simp
    cases Hwt
    . case T_Abs τ2 Hewt =>
      constructor
      rw [<-List.cons_append] at Hewt
      specialize IH Γ (τ1 :: Γ') v τ2 τ' Hewt Hvwt
      simp at IH
      trivial
  | App e1 e2 IH1 IH2 | Pair e1 e2 IH1 IH2 =>
    intro Γ Γ' v τ τ' Hwt Hvwt
    cases Hwt
    . simp
      constructor
      . apply IH1
        all_goals trivial
      . apply IH2
        all_goals trivial
  | Zro | Tru | Fls =>
    intro Γ Γ' v τ τ' Hwt Hvwt
    simp
    cases Hwt
    constructor
  | Fst e IH | Snd e IH | IsZero e IH | Succ e IH =>
    intro Γ Γ' v τ τ' Hwt Hvwt
    simp
    cases Hwt
    constructor
    apply IH
    all_goals trivial
  | If e1 e2 e3 IH1 IH2 IH3 =>
    intro Γ Γ' v τ τ' Hwt Hvwt
    simp
    cases Hwt
    constructor
    . apply IH1
      all_goals trivial
    . apply IH2
      all_goals trivial
    . apply IH3
      all_goals trivial

theorem subst_1_pres_typing : forall Γ e v τ τ',
  ((τ' :: Γ) ⊢ e : τ) ->
  ([] ⊢ v : τ') ->
  Γ ⊢ (e[v]) : τ := by

  intros Γ e v τ τ' Hwt Hvwt
  have h : Γ = [] ++ Γ := by simp
  rw [h]
  apply subst_pres_typing
  all_goals trivial

theorem preservation : forall e e' τ,
  ([] ⊢ e : τ) ->
  (e >-> e') ->
  [] ⊢ e' : τ := by

  intros e e' τ Hwt Heval
  revert e'
  generalize hΓ : [] = Γ
  rw [hΓ] at Hwt
  induction Hwt with
  | T_Var =>
   intros
   contradiction
  | T_Abs =>
    intros
    contradiction
  | T_App Γ' τ1 τ2 e1 e2 Hwt1 Hwt2 IH1 IH2 =>
    intros e' Heval
    cases Heval
    . case E_App1 e1' Heval =>
      specialize IH1 hΓ e1' Heval
      constructor
      all_goals trivial
    . case E_App2 v Hvalue Heval =>
      specialize IH2 hΓ v Heval
      constructor
      all_goals trivial
    . case E_AppAbs τ' e' Hvalue =>
      cases Hwt1
      . case T_Abs Hwt' =>
        rw [<-hΓ] at Hwt2
        apply subst_1_pres_typing
        all_goals trivial
  | T_Zero Γ =>
    intros
    contradiction
  | T_Succ Γ' e1 Hwt IH =>
    intros e' Heval
    cases Heval
    . case E_Succ e1' He1 =>
      specialize IH hΓ e1' He1
      constructor
      trivial
  | T_IsZero Γ' e' Hwt IH =>
    intros e' Heval
    cases Heval
    . case E_IsZero e1' He1 =>
      specialize IH hΓ e1' He1
      constructor
      trivial
    . case E_IsZeroTrue => constructor
    . case E_IsZeroFalse => constructor
  | T_Tru Γ' =>
    intros
    contradiction
  | T_Fls Γ' =>
    intros
    contradiction
  | T_If Γ' e1 e2 e3 τ' Hwt1 Hwt2 Hwt3 IH1 IH2 IH3 =>
    intros e' Heval
    cases Heval
    . case E_If e1' H1 =>
      specialize IH1 hΓ e1' H1
      constructor
      all_goals trivial
    . case E_IfTrue => trivial
    . case E_IfFalse => trivial
  | T_Pair Γ' e1 e2 τ1 τ2 Hwt1 Hwt2 IH1 IH2 =>
    intros e' Heval
    cases Heval
    . case E_Pair1 e1' He1 =>
      specialize IH1 hΓ e1' He1
      constructor
      trivial
      trivial
    . case E_Pair2 e2' Hvalue He2 =>
      specialize IH2 hΓ e2' He2
      constructor
      trivial
      trivial
  | T_Fst Γ' e' τ1 τ2 Hwt IH =>
    intros e' Heval
    cases Heval
    . case E_Fst e1' He1 =>
      specialize IH hΓ e1' He1
      constructor
      trivial
    . case E_FstPair =>
      cases Hwt
      trivial
  | T_Snd Γ' e' τ1 τ2 Hwt IH =>
    intros e' Heval
    cases Heval
    . case E_Snd e1' He1 =>
      specialize IH hΓ e1' He1
      constructor
      trivial
    . case E_SndPair =>
      cases Hwt
      trivial

theorem normalizing : forall Γ e τ,
  (Γ ⊢ e : τ) ->
  exists e', (e >->* e') /\ is_value e' := by
  sorry
