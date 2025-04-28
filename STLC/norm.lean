import STLC.defs
import STLC.step
open term
open type
open step
open wt
open multistep


@[reducible]
def substitution : Type := Nat -> term

@[reducible, simp]
def idSubst : substitution := (fun i => Var i)

@[simp]
def extSubst (γ  : substitution) e :=
  fun i => if i = 0 then e else up_term (γ (i - 1)) (i - 1)

theorem ext_id_subst : idSubst = extSubst idSubst (Var 0) :=
by
  apply funext
  intros x
  unfold extSubst
  simp
  induction x
  . simp
  . case succ n IH =>
    simp


@[simp]
def simulsubst (e : term) (γ : substitution) :=
    match e with
  | Var i => γ i
  | Abs τ e => Abs τ (simulsubst e (extSubst γ (Var 0)))
  | App e1 e2 => App (simulsubst e1 γ) (simulsubst e2 γ)
  | Zro => Zro
  | Succ e => Succ (simulsubst e γ)
  | IsZero e => IsZero (simulsubst e γ)
  | Fls => Fls
  | Tru => Tru
  | If e1 e2 e3 => If (simulsubst e1 γ) (simulsubst e2 γ) (simulsubst e3 γ)
  | Pair e1 e2 => Pair (simulsubst e1 γ) (simulsubst e2 γ)
  | Fst e => Fst (simulsubst e γ)
  | Snd e => Snd (simulsubst e γ)

notation e "[" γ "]" => simulsubst e γ

@[simp]
def simulsubst_one e e' n :=
  e [fun i => if i = n then e' else if i > n then Var (i - 1) else Var i]

theorem simulsubst_id e :
  e = simulsubst e idSubst := by

  induction e
  all_goals (simp; try trivial)
  . case Abs _ e' IH =>
    rw [<-ext_id_subst]
    trivial

@[simp]
def lr (τ : type) (e : term) : Prop :=
  match τ with
  | TNat => (e >->* Zro) \/ (exists v, (e >->* Succ v) /\ is_value v)
  | TBool => (e >->* Tru) \/ (e >->* Fls)
  | Mult τ1 τ2 =>
      exists v1 v2, (e >->* Pair v1 v2) /\ is_value v1 /\ is_value v2 /\
        lr τ1 v1 /\ lr τ2 v2
  | Arr τ1 τ2 =>
      exists e2, (e >->* Abs τ1 e2) /\
      forall e1, lr τ1 e1 -> lr τ2 (simulsubst_one e2 e1 0)

theorem lr_steps_to_value (τ : type) (e : term) :
  lr τ e ->
  exists e', (e >->* e') /\ is_value e' := by

  intros Hlr
  cases τ
  all_goals (simp at Hlr)
  . cases Hlr
    . exists Zro
    . case inr h =>
      let ⟨v, Heval, Hvalue⟩ := h
      exists (Succ v)
  . cases Hlr
    . exists Tru
    . exists Fls
  . case Mult τ1 τ2 =>
    let ⟨e1, e2, Heval, Hval1, HVal2, hlr1, hlr2⟩ := Hlr
    exists (Pair e1 e2)
  . case Arr τ1 τ2 =>
    let ⟨e2, Heval, HImp⟩ := Hlr
    exists (Abs τ1 e2)

theorem lr_pres_red_one : forall τ e e',
  lr τ e ->
  (e >-> e') ->
  lr τ e' := by

  intros τ
  cases τ with
  | TBool =>
    intros e e' He' Heval
    cases He'
    . case inl h =>
      left
      cases h
      . case M_refl =>
        contradiction
      . case M_one e2 Hone Hmany =>
        have h: e2 = e' := by
          apply step_deterministic
          all_goals trivial
        subst h
        apply Hmany
    . case inr h =>
      right
      cases h
      . case M_refl =>
        contradiction
      . case M_one e2 Hone Hmany =>
        have h: e2 = e' := by
          apply step_deterministic
          all_goals trivial
        subst h
        apply Hmany
  | TNat =>
    intros e e' He' HEval
    cases He'
    . case inl h =>
      left
      cases h
      . case M_refl =>
        contradiction
      . case M_one e2 Hone Hmany =>
        have h: e2 = e' := by
          apply step_deterministic
          all_goals trivial
        subst h
        apply Hmany
    . case inr h =>
      right
      let ⟨v, Hstep, Hvalue⟩ := h; clear h
      generalize hSucc : Succ v = r
      rw [hSucc] at Hstep
      induction Hstep
      . case M_refl e'' =>
        exfalso
        rw [<-hSucc] at HEval
        apply value_does_not_step (Succ v)
        unfold is_value
        trivial
        exists e'
      . case M_one e1' e2' e3' Hone Hmany IH =>
        have h: e2' = e' := by
          apply step_deterministic
          all_goals trivial
        subst h
        exists v
        rw [<-hSucc] at Hmany
        apply And.intro
        apply Hmany
        trivial
  | Mult τ1 τ2 =>
    intros e e' He' Heval
    simp at He'
    let ⟨v1, v2, HStep, Hval1, Hval2, Hlr1, Hlr2⟩ := He'; clear He'
    simp
    generalize hPair : Pair v1 v2 = r
    rw [hPair] at HStep
    induction HStep
    . case M_refl e'' =>
      exfalso
      rw [<-hPair] at Heval
      apply value_does_not_step (Pair v1 v2)
      unfold is_value
      apply And.intro
      all_goals (try trivial)
      exists e'
    . case M_one e1' e2' e3' Hone Hmany IH =>
      have h: e2' = e' := by
          apply step_deterministic
          all_goals trivial
      subst h
      rw [<-hPair] at Hmany
      exists v1, v2
  | Arr τ1 τ2 =>
    intros e e' He' Heval
    simp at He'
    let ⟨v, HStep, HImp⟩ := He'; clear He'
    simp
    cases HStep
    . case M_refl =>
      contradiction
    . case M_one e2' Hone Hmany =>
      have h : e2' = e' := by
        apply step_deterministic
        all_goals trivial
      subst h
      exists v

theorem head_expansion_one : forall τ e e',
  lr τ e' ->
  (e >-> e') ->
  lr τ e := by

  intros τ
  cases τ with
  | TBool =>
    intros e e' He' Heval
    simp at He'
    cases He'
    . left
      constructor
      trivial
      trivial
    . right
      constructor
      trivial
      trivial
  | TNat =>
    intros e e' He' Heval
    simp at He'
    cases He'
    . left
      constructor
      trivial
      trivial
    . case inr h =>
      right
      let ⟨v, Heval, HValue⟩ := h
      exists v
      constructor; constructor
      all_goals trivial
  | Mult τ1 τ2 =>
    intros e e' He' Heval
    simp at He'
    let ⟨e1, e2, Heval', Hlr1, Hlr2⟩ := He'
    exists e1, e2
    constructor
    constructor
    trivial
    trivial
    constructor
    trivial
    trivial
  | Arr τ1 τ2 =>
    intros e e' He' Heval
    simp at He'
    let ⟨e2, Heval', HImp⟩ := He'
    exists e2
    constructor
    constructor
    trivial
    trivial
    apply HImp

theorem lr_pres_red_many : forall τ e e',
  lr τ e ->
  (e >->* e') ->
  lr τ e' := by

  intros τ e e' Hlr Hstep
  induction Hstep
  . trivial
  . case M_one e e' e'' Hone Hmany IH =>
    apply IH
    apply lr_pres_red_one
    all_goals trivial

theorem head_expansion_many : forall τ e e',
  lr τ e' ->
  (e >->* e') ->
  lr τ e := by

  intros τ e e' Hlr Hstep
  induction Hstep
  . trivial
  . case M_one e e' e'' Hone Hmany IH =>
    specialize IH Hlr
    apply head_expansion_one
    all_goals trivial

@[simp]
def subst_lr (Γ : context) (γ : substitution) :=
  forall (i : Nat) τ,
  Γ[i]? = some τ -> lr τ (γ i)

notation Γ " ⊨ " γ => subst_lr Γ γ

def emp_subst_lr : forall γ, [] ⊨ γ := by
  intros γ
  intros i τ Hτ
  contradiction

def sem_wt (Γ : context) (e : term) (τ : type) :=
  forall γ, (Γ ⊨ γ) -> lr τ (e [γ])

notation Γ " ⊨ " e " : " τ => sem_wt Γ e τ

theorem up_term_at_zero e n e' :
  up_term e n = simulsubst_one (up_term e n) e' n := by

  revert e' n
  induction e
  all_goals (intros n e')
  all_goals (simp; try trivial)
  . case Var i => sorry
  . case Abs τ e IH =>
    unfold simulsubst_one at IH
    unfold extSubst
    specialize (IH (n + 1))
    sorry
  . case App => sorry
  . case Succ => sorry
  . case IsZero => sorry
  . case If => sorry
  . case Pair => sorry
  . case Fst => sorry
  . case Snd => sorry

theorem ext_subst_zero_subst γ e e' :
  (e [extSubst γ e']) = simulsubst_one (e [extSubst γ (Var 0)]) e' 0 := by

  unfold extSubst
  induction e
  all_goals (simp; try trivial)
  . case Var i =>
    cases i
    . simp
    . case succ i =>
      simp
      sorry
  . case Abs τ e IH =>
    unfold extSubst
    sorry

theorem simulsubst_one_subst e e' n :
  simulsubst_one e e' n = subst e n e' := by

  revert e' n
  induction e
  all_goals (intros e' n)
  all_goals (simp; try trivial)
  . case Abs τ e IH =>
    sorry
  . case App => sorry
  . case Succ => sorry
  . case IsZero => sorry
  . case If => sorry
  . case Pair => sorry
  . case Fst => sorry
  . case Snd => sorry

theorem subst_lr_extend Γ γ τ e:
  (Γ ⊨ γ) ->
  lr τ e ->
  (τ :: Γ) ⊨ extSubst γ e := by

  unfold subst_lr
  unfold extSubst
  intros Hγ Hlr i τ' Hctx
  match i with
  | 0 =>
      simp;
      sorry
  | .succ j =>
      simp at Hctx
      simp;
      sorry



/- theorem fundamental_lemma (Γ : context) (e : term) (τ : type) :
  (Γ ⊢ e : τ) ->
  Γ ⊨ e : τ := by

  intros Hwt
  induction Hwt with
 | T_Var Γ i τ H =>
    intros γ Hγ
    specialize Hγ i τ H
    simp
    trivial
  | T_Zero Γ | T_Tru Γ =>
    intros γ Hγ
    simp
    left
    constructor
  | T_Succ Γ e1 Hwt IH =>
    intros γ Hγ
    simp
    right
    specialize IH γ Hγ
    simp at IH
    cases IH
    . case inl h =>
      exists Zro
      constructor
      apply multistep_congr_succ
      all_goals trivial
    . case inr h =>
      let ⟨v, Heval, Hvalue⟩ := h
      exists (Succ v)
      constructor
      apply multistep_congr_succ
      all_goals trivial
  | T_IsZero Γ' e' Hwt IH =>
    intros γ Hγ
    simp
    specialize IH γ Hγ
    simp at IH
    cases IH
    . case inl h =>
      left
      apply multistep_comp
      apply multistep_congr_isZero
      all_goals (try trivial)
      apply M_one
      apply E_IsZeroTrue
      apply M_refl
    . case inr h =>
      let ⟨v, Heval, Hvalue⟩ := h
      right
      apply multistep_comp
      apply multistep_congr_isZero
      all_goals (try trivial)
      apply M_one
      apply E_IsZeroFalse
      trivial
      apply M_refl
  | T_Fls Γ' =>
    intros γ Hγ
    simp
    right
    constructor
  | T_If Γ e1 e2 e3 τ Hwt1 Hwt2 Hwt3 IH1 IH2 IH3 =>
    intros γ Hγ
    simp
    specialize IH1 γ Hγ
    specialize IH2 γ Hγ
    specialize IH3 γ Hγ
    cases IH1
    . case inl h =>
      apply head_expansion_many
      apply IH2
      apply multistep_comp
      apply multistep_congr_if
      all_goals (try trivial)
      apply M_one
      apply E_IfTrue
      apply M_refl
    . case inr h =>
      apply head_expansion_many
      apply IH3
      apply multistep_comp
      apply multistep_congr_if
      all_goals (try trivial)
      apply M_one
      apply E_IfFalse
      apply M_refl
  | T_Pair Γ e1 e2 τ1 τ2 Hwt1 Hwt2 IH1 IH2 =>
    intros γ Hγ
    simp
    specialize IH1 γ Hγ
    specialize IH2 γ Hγ
    have HVal1 := lr_steps_to_value τ1 (e1[γ]) IH1
    have HVal2 := lr_steps_to_value τ2 (e2[γ]) IH2
    let ⟨v1, HEval1, Hval1⟩ := HVal1
    let ⟨v2, HEval2, Hval2⟩ := HVal2
    exists v1, v2
    constructor
    apply multistep_congr_pair
    all_goals (try trivial)
    constructor; trivial; constructor; trivial; constructor
    apply lr_pres_red_many
    all_goals (try trivial)
    apply lr_pres_red_many
    all_goals trivial
  | T_Fst Γ e τ1 τ2 Hwt IH =>
    intros γ Hγ
    simp
    specialize IH γ  Hγ
    let ⟨v1, v2, Heval, Hval1, Hval2, hlr1, hlr2⟩ := IH
    apply head_expansion_many
    apply hlr1
    apply multistep_comp
    apply multistep_congr_fst
    all_goals (try trivial)
    apply M_one
    apply E_FstPair
    trivial
    trivial
    apply M_refl
  | T_Snd Γ' e' τ1 τ2 Hwt IH =>
    intros γ Hγ
    simp
    specialize IH γ  Hγ
    let ⟨v1, v2, Heval, Hval1, Hval2, hlr1, hlr2⟩ := IH
    apply head_expansion_many
    apply hlr2
    apply multistep_comp
    apply multistep_congr_snd
    all_goals (try trivial)
    apply M_one
    apply E_SndPair
    trivial
    trivial
    apply M_refl
  | T_Abs Γ' τ1 τ2 e' Hwt IH =>
    intros γ Hγ
    exists (e'[extSubst γ (Var 0)])
    apply And.intro
    apply M_refl
    intros e1 Hlr
    have h : (τ1 :: Γ')  ⊨ extSubst γ e1 := by
      apply subst_lr_extend
      all_goals trivial
    specialize IH (extSubst γ e1) h
    rw [<-ext_subst_zero_subst]
    trivial
  | T_App Γ' τ1 τ2 e1 e2 Hwt1 Hwt2 IH1 IH2 =>
    intros γ Hγ
    specialize IH1 γ Hγ
    specialize IH2 γ Hγ
    simp at IH1
    let ⟨e2', Hstep, HImp⟩ := IH1; clear IH1
    have hval := lr_steps_to_value τ1 (e2[γ]) IH2
    let ⟨e2'', Hstep2, HVal⟩ := hval; clear hval
    have hlr' := lr_pres_red_many τ1 (e2[γ]) e2'' IH2 Hstep2
    specialize HImp (e2'') hlr'
    apply head_expansion_many
    apply HImp
    simp
    apply multistep_comp
    apply multistep_congr_app
    all_goals (try trivial)
    apply M_one
    apply E_AppAbs
    all_goals (try trivial)
    rw [<-simulsubst_one_subst]
    simp
    apply M_refl

 theorem normalizing : forall e τ,
  ([] ⊢ e : τ) ->
  exists e', (e >->* e') /\ is_value e' := by

  intros e τ Hwt
  have HsemWt := fundamental_lemma [] e τ Hwt
  simp at HsemWt
  specialize HsemWt idSubst (emp_subst_lr idSubst)
  rw [<-simulsubst_id] at HsemWt
  apply lr_steps_to_value
  all_goals trivial
