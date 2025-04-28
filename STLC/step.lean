import STLC.defs
open term
open type
open step
open wt
open multistep

theorem step_deterministic e1 e2 e3 :
  (e1 >-> e2) ->
  (e1 >-> e3) ->
  e2 = e3 := by

  intros H1 H2
  revert e3
  induction H1
  all_goals (intros e3 H2)
  . case E_App1 e1' e1'' e2' Hstep IH =>
    cases H2
    . case E_App1 e11 Hstep' =>
      congr
      apply IH
      trivial
    . case E_App2 e2' HVal Istep' =>
      exfalso
      apply value_does_not_step
      trivial
      exists e1''
    . case E_AppAbs τ e' HValue =>
      contradiction
  . case E_App2 v e2' e2'' Hvalue Hstep IH =>
    cases H2
    . case E_App1 e11 Hstep' =>
      exfalso
      apply value_does_not_step
      trivial
      exists e11
    . case E_App2 e2'' HVal Istep' =>
      congr
      apply IH
      trivial
    . case E_AppAbs τ e' HValue =>
      exfalso
      apply value_does_not_step
      trivial
      exists e2'
  . case E_AppAbs τ τ' e' HValue =>
    cases H2
    . case E_App1 e11 Hstep' =>
      contradiction
    . case E_App2 e2'' HVal Istep' =>
      exfalso
      apply value_does_not_step
      apply HValue
      exists e2''
    . case E_AppAbs =>
      trivial
  . case E_Succ e1' e2' HStep IH =>
    cases H2
    congr
    apply IH
    trivial
  . case E_IsZero e1' e2' HStep IH =>
    cases H2
    . case E_IsZero e' HStep' =>
      congr
      apply IH
      trivial
    . case E_IsZeroTrue =>
      contradiction
    . case E_IsZeroFalse v HValue =>
      cases HStep
      . case E_Succ e' HStep' =>
        exfalso
        apply value_does_not_step
        apply HValue
        exists e'
  . case E_IsZeroTrue =>
    cases H2
    contradiction
    trivial
  . case E_IsZeroFalse =>
    cases H2
    . case E_IsZero v HVal e' HStep =>
      cases HStep
      . case E_Succ e'' HStep =>
        exfalso
        apply value_does_not_step
        apply HVal
        exists e''
    . trivial
  . case E_If e1' e1'' e2' e3' Hstep IH =>
    cases H2
    . case E_If e1''' Hstep' =>
      congr
      apply IH
      trivial
    . case E_IfTrue =>
      contradiction
    . case E_IfFalse =>
      contradiction
  . case E_IfTrue e2' e3' =>
    cases H2
    contradiction
    trivial
  . case E_IfFalse e2' e3' =>
    cases H2
    contradiction
    trivial
  . case E_Pair1 e1' e1'' e2' HStep IH =>
    cases H2
    . case E_Pair1 e' Hstep' =>
      congr
      apply IH
      trivial
    . case E_Pair2 e2'' Hvalue Hstep' =>
      exfalso
      apply value_does_not_step
      trivial
      exists e1''
  . case E_Pair2 v e2' e2'' HValue Hstep IH =>
    cases H2
    . case E_Pair1 e' Hstep' =>
      exfalso
      apply value_does_not_step
      trivial
      exists e'
    . case E_Pair2 e' Hvalue' Hstep' =>
      congr
      apply IH
      trivial
  . case E_Fst e1' e2' Hstep IH =>
    cases H2
    . case E_Fst e' HStep' =>
      congr
      apply IH
      trivial
    . case E_FstPair v HVal1 Hval2 =>
      exfalso
      apply value_does_not_step (Pair e3 v)
      unfold is_value
      apply And.intro
      all_goals (try trivial)
      exists e2'
  . case E_FstPair v1 v2 Hv1 Hv2 =>
    cases H2
    . case E_Fst e' Hstep =>
      exfalso
      apply value_does_not_step (Pair v1 v2)
      unfold is_value
      apply And.intro
      all_goals (try trivial)
      exists e'
    . trivial
  . case E_Snd e1' e2' Hstep IH =>
    cases H2
    . case E_Snd e' HStep' =>
      congr
      apply IH
      trivial
    . case E_SndPair v HVal1 Hval2 =>
      exfalso
      apply value_does_not_step (Pair v e3)
      unfold is_value
      apply And.intro
      all_goals (try trivial)
      exists e2'
  . case E_SndPair v1 v2 Hv1 Hv2 =>
    cases H2
    . case E_Snd e' Hstep =>
      exfalso
      apply value_does_not_step (Pair v1 v2)
      unfold is_value
      apply And.intro
      all_goals (try trivial)
      exists e'
    . trivial

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
