import LeanSubst
import Lilac.Vect

open LeanSubst
open Vect

def Vect.drop (v : (Vect (n + 1) Q)) : Vect n Q := v.uncons.2


protected def Vect.reprPrec [Repr T] : {n : Nat} -> Vect n T -> Nat -> Std.Format
| 0, _, _ => ""
| 1, v, _ => repr (v 0)
| _ + 1, v, i =>
  let ⟨h , t⟩ := v.uncons
  (repr h) ++ ", " ++ (Vect.reprPrec t i)

instance [Repr T] : Repr (Vect n T) where
  reprPrec v n := "v[" ++ Vect.reprPrec v n ++ "]"

@[simp]
theorem Vect.nil_singleton (v1 v2 : Vect 0 T) : v1 = v2 := by
  funext; case _ i =>
  cases i; case _ i p => cases p

@[simp]
instance : GetElem (Vect n α) (Fin n) α (λ _ _ => True) where
  getElem xs i _ := xs i

@[simp]
instance : GetElem? (Vect n α) (Fin n) α (λ _ _ => True) where
  getElem? xs i := .some (xs i)

@[simp]
theorem get_cons_head {t : Vect T n} : (h::t) 0 = h := by simp [Vect.cons]

@[simp]
theorem get_cons_tail_succ {t : Vect T n} : (h::t) (Fin.succ i) = t i := by
  simp [Vect.cons];

def Vect.length (_ : Vect n A) : Nat := n

theorem Vect.length_bound : (v : Vect n A) -> v.length = n := by
  intro v
  unfold Vect.length
  induction n <;> (simp at *)

@[simp]
def Vect.sum : {n : Nat} -> Vect n Nat -> Nat
| 0, _ => 0
| _ + 1, ts => ts 0 + ts.drop.sum



theorem length_coerce: ∀ n, Vect.length v = n -> (Vect.to_list v).length = n := by
apply v.induction <;> simp [Vect.length] at *


def Vect.seq_lemma (vs : Vect n (Option Q)) :
  (Σ' (i : Fin n), ¬ (vs i).isSome) ⊕ ((i : Fin n) -> Σ' A, (vs i) = some A)
:= by {
    induction n
    case _ =>
      apply Sum.inr; intro i
      apply Fin.elim0 i
    case _ n ih =>
      generalize zdef : uncons vs = z at *
      rcases z with ⟨h, t⟩
      have lem := Vect.uncons_iff.1 zdef
      cases h
      case none =>
        apply Sum.inl; apply PSigma.mk 0
        rw [lem]; simp
      case some h =>
        replace ih := ih t
        cases ih
        case _ ih =>
          rcases ih with ⟨k, ih⟩
          apply Sum.inl; apply PSigma.mk (Fin.succ k)
          rw [lem]; simp at *; exact ih
        case _ ih =>
          apply Sum.inr; intro i
          cases i using Fin.cases
          case _ => rw [lem]; simp; apply PSigma.mk h; rfl
          case _ i => rw [lem]; simp; apply ih i
  }

def Vect.seq (vs : Vect n (Option Q)) : Option (Vect n Q) :=
  match seq_lemma vs with
  | .inl h => none
  | .inr h => some (λ i => Option.get (vs i) (by {
    replace h := h i
    rcases h with ⟨t, e⟩
    rw [e]; simp
  }))


theorem Vect.seq_sound {vs : Vect n (Option Q)} {vs' : Vect n Q}:
  vs.seq = some vs' ->
  ∀ i, (vs i) = some (vs' i) := by
intro h i;
apply Vect.induction
  (A := Option Q)
  (motive := λ x v => ∀ vs' : Vect x Q, ∀ i, v.seq = some vs' -> v i = some (vs' i))
  (nil := by intro h'; simp)
  (cons := by
    intro x hd tl ih vs' j; simp [seq];
    generalize zdef : (Vect.cons hd tl).seq_lemma = z;
    cases z <;> simp at *
    case inr v =>
    replace v := v j
    intro h'
    have jeq : j = j := by rfl
    replace h' := congrFun h' j;
    rcases v with ⟨A, v⟩
    simp only [v] at h'; simp at h'; rw[<-h']; assumption
    )
  vs vs' i h

def Vect.elems_eq_to [BEq Q] {n : Nat} (e : Q) (vs : Vect n Q) : Bool :=
  vs.fold true (λ c acc => c == e && acc)

theorem Vect.elems_eq_to_sound [BEq Q] [LawfulBEq Q] {e : Q} {vs : Vect n Q} :
  vs.elems_eq_to e = true ->
  ∀ i, (vs i) = e := by
apply vs.induction <;> simp [Vect.elems_eq_to] at *
case _ =>
  intro n hd tl ih e h
  subst hd; replace ih := ih h
  intro i'
  induction i' using Fin.induction <;> simp at *
  case _ i _ => apply ih i


theorem quantifier_flip {Q Q' : Type} {v : Vect n Q} (f : Q -> Option Q') :
  (∀ i, ∃ T, f (v i) = some T) ->
  ∃ (T' : Vect n Q'), ∀ i, f (v i) = some (T' i) := by
  intro h
  generalize T'def : Vect.seq (f <$> v) = T' at *
  cases T'
  case none =>
    exfalso
    -- completeness of seq
    unfold Vect.seq at T'def;
    generalize slem : Vect.seq_lemma (f <$> v)= sl at *
    cases sl <;> simp at *
    case inl i =>
      rcases i with ⟨i, h'⟩
      -- unfold Vect.map at h'
      replace h := h i
      rcases h with ⟨T , h⟩
      rw[h] at h'; simp at h'
  case some T' =>
  exists T'
  · intro i;
    replace h := h i
    rcases h with ⟨q', h⟩
    have lem := Vect.seq_sound T'def
    replace lem := lem i; simp at lem; assumption


-- Returns the 1st element if all the elements are equal
def Vect.get_elem_if_eq [BEq Q][LawfulBEq Q] (vs : Vect n Q) : Option Q :=
match n with
| 0 => none
| _ + 1 => match vs.uncons with
  | ⟨h, vs'⟩ => if Vect.elems_eq_to h vs' then return h else none

theorem Vect.get_elem_if_eq_sound[BEq Q] [LawfulBEq Q] {vs : Vect n Q} {t : Q} :
  vs.get_elem_if_eq = some t ->
  ∀ i, vs i = t := by
apply vs.induction
case _ => simp
case _ =>
  intro n hd tl ih
  simp [Vect.get_elem_if_eq];
  intro h1 h2
  subst t; intro i
  induction i using Fin.induction <;> simp at *
  case _ i h =>
    have lem := Vect.elems_eq_to_sound h1
    apply lem i


-- returns the first element that is not none
def Vect.any {n : Nat} (vs : Vect n (Option T)) : Option T :=
  match n with
  | 0 => none
  | _ + 1 => match vs.uncons with
    | ⟨h, tl⟩ => if h.isSome then h else tl.any


-- Proof that Any actually matches the first element
theorem Vect.any_returns_first {t : T} : ∀ n, {vs : Vect n (Option T)} ->
  vs.any = some t ->
  ∃ i, vs i = some t ∧ ∀ j, j < i -> vs j = none := by
apply Vect.induction <;> simp [Vect.any]
case _ =>
  intro n hd tl ih h
  split at h
  case _ => exists 0; simp; exact h
  case _ =>
    replace ih := ih h;
    rcases ih with ⟨i, ih1, ih2⟩
    exists Fin.succ i
    apply And.intro
    case _ => simp; exact ih1
    case _ =>
      intro j
      induction j using Fin.induction <;> simp at *
      case _ h => exact h
      case _ j ih h =>
        intro le; replace ih2 := ih2 _ le; exact ih2


def Vect.zip {n} (ps: Vect n Q) (cs : Vect n Q') : Vect n (Q × Q') := λ i => (ps i , cs i)

theorem Vect.zip_sound {n} {ps: Vect n Q} {cs : Vect n Q'} :
  ∀ i, (ps.zip cs i) = (ps i , cs i) := by
intro i; simp [Vect.zip]


theorem Vect.map_cons {f : Q -> P} {v : Vect n Q} {v' : Vect (n + 1) P} {q : Q} :
  v' = (λ i => f ((Vect.cons q v) i)) ->
  v' = Vect.cons (f q) (λ i => (f (v i))) := by
intro h; subst h; funext i
induction i using Fin.induction <;> simp [Vect.cons]
