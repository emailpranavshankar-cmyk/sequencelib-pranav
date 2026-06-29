import Mathlib

variable (A B C D : Prop)

example : A ∧ (A → B) → B :=
fun h => h.right h.left

example : A → ¬ (¬ A ∧ B) :=
fun a => fun notab => notab.left a

example : ¬ (A ∧ B) → (A → ¬ B) :=
fun notab => fun a => fun b => notab (And.intro a b)




example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
Or.elim h₁  (fun ha : A => Or.inl (h₂ ha) ) (fun hb: B => Or.inr (h₃ hb) )

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
fun neither => Or.elim neither (fun a => h.left a) (fun b => h.right b)


example : ¬ (A ↔ ¬ A) := by
  by_contra h
  have dirone : A → ¬ A := h.mp
  have dirtwo : ¬ A → A := h.mpr
  have na : ¬ A := fun a => dirone a a
  have a : A := dirtwo na
  exact na a


def m : Nat := 1       -- m is a natural number
def n : Nat := 0
def b1 : Bool := true  -- b1 is a Boolean
def b2 : Bool := false

#check b1 || b2
#check m
#eval b1 && b2

variable (p q : Prop)

theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp

theorem teetwo : ∀ {p q : Prop}, p → q → p :=
fun {p q} hp hq => hp

%% Note that a "proof" of p implies q is just a function that sends a proof of p to a proof of q. fun (hp hq) to hp because hp hq gives proof of p implies q, then fun that to hp.

variable (r : Prop)
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp


variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
Iff.intro
(fun hp : p ∧ q => And.intro (And.right hp) (And.left hp))
(fun hq : q ∧ p => And.intro (And.right hq) (And.left hq) )
example : p ∨ q ↔ q ∨ p :=
Iff.intro
(fun hp : p ∨ q => Or.elim hp (fun hp1 => Or.inr hp1) (fun hp2 => Or.inl hp2))
(fun hq : q ∨ p => Or.elim hq (fun hq1 => Or.inr hq1) (fun hq2 => Or.inl hq2))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
(fun h1 : (p ∧ q) ∧ r => And.intro (And.left (And.left h1)) (And.intro (And.right (And.left h1)) (And.right h1)))
(fun h2 : p ∧ (q ∧ r) => And.intro (And.intro (And.left h2) (And.left (And.right h2))) (And.right (And.right h2)))



example : ¬p → (p → q) :=
   fun (notp : ¬p) => fun (contra : p) => absurd contra notp
example : p ∧ ¬q → ¬(p → q) :=
   fun notimp => fun pimp => And.right notimp (pimp (And.left notimp))
example : (¬p ∨ q) → (p → q) :=
   fun paq => fun piq => Or.elim paq (fun notp=> absurd piq notp) (fun hq => hq)
example {p q r : Prop} : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun nested => fun qr => nested (And.left qr) (And.right qr))
    (fun anded => fun peck => fun quack => anded (And.intro peck quack))
example {p : Prop} : p ∨ False ↔ p :=
  Iff.intro
    (fun deeor => Or.elim deeor (fun p => p) (fun hfalse => by
      exfalso
      exact hfalse))
    (fun deceiver => Or.inl deceiver)



open Classical

variable (p q r : Prop)

example {p q r : Prop} : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun mixie =>
    Or.elim (Classical.em q)
    (fun queen => Or.inl (fun _ => queen))
    (fun notq => Or.inr (fun packard => Or.elim (mixie packard) (fun q1 => absurd q1 notq) (fun romeo => romeo)))
example : ¬(p ∧ q) → ¬p ∨ ¬q := fun notboth => Or.elim (Classical.em p) (fun hewlett => Or.inr (fun quackard => notboth (And.intro hewlett quackard)) )
(fun notp => Or.inl (notp) )


open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := by
  intro ex
  rcases ex with ⟨_, hx⟩
  exact hx


example (a : α) : r → (∃ _ : α, r) := by
   intro rome
   use a



example {α : Type} {p : α → Prop} {r : Prop} : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  · intro expx
    rcases expx with ⟨xored, hx⟩

    constructor
    ·
      use xored
      exact And.left hx

    ·  exact And.right hx


  · intro expxr
    rcases expxr with ⟨exped, px⟩
    rcases exped with ⟨pax, romana⟩
    use pax



example {α : Type} {p q : α → Prop} : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro pork
    rcases pork with ⟨w, pa | qa⟩
    left
    use w
    right
    use w
  · intro mixy
    rcases mixy with map | maq
    · rcases map with ⟨ap, pap⟩
      use ap
      left
      exact pap
    · rcases maq with ⟨aq, paq⟩
      use aq
      right
      exact paq


example {α : Type} {p : α → Prop} : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  · intro everything
    intro falsifier
    rcases falsifier with ⟨quack, prick⟩
    have duck := everything quack
    exact prick duck


  · intro pax
    intro x
    by_contra hx
    apply pax
    exact ⟨x, hx⟩









example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
    constructor
    · intro exp
      intro nall
      rcases exp with ⟨pan, wan⟩
      have pad := nall pan
      exact pad wan
    · intro doubleneg
      by_contra it_exists
      apply doubleneg
      intro x
      intro hx
      exact it_exists ⟨x, hx⟩









example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  · intro nexper
    intro x
    by_contra this
    apply nexper
    use x
  · intro do_it_all
    intro falsify
    rcases falsify with ⟨stepmother, screams⟩
    have stepmother_disabled := do_it_all stepmother
    exact stepmother_disabled screams




example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
   constructor
   · intro all_implies
     intro always_r
     rcases always_r with ⟨it, pit⟩
     have a_implies := all_implies it
     exact a_implies pit

   · intro exper
     intro x
     intro pix
     have ra := exper ⟨x, pix⟩
     exact ra

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
    constructor
    ·  intro experience
       intro pax_americana
       rcases experience with ⟨time, passer⟩
       have long_pax := pax_americana time
       have sun_god := passer long_pax
       exact sun_god


    ·  intro birds_nest
       by_cases hr: r
       · exact ⟨a, fun _=> hr⟩
       · by_contra madness
         push_neg at madness
         apply hr
         apply birds_nest
         intro x
         apply madness at x
         exact x.left
