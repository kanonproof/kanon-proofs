/-!
# Tax never falls as income rises (#7)

A tax schedule is brackets (income from `lo` to `hi` taxed at `rate` basis points), applied to
income after a tax-free allowance, less a rebate. This is the shape of the US, UK and South African
schedules in the app. We prove that more income never means less tax, and so the extra tax on a
gain stacked on top of other income is never negative.
-/

namespace Kanon.Brackets

structure Bracket where
  lo : Nat
  hi : Nat
  rate : Nat

/-- The part of income `x` that falls inside the bracket. -/
def slice (x : Nat) (b : Bracket) : Nat := min x b.hi - min x b.lo

/-- Tax in basis points of currency units, before dividing by 10,000. -/
def taxBp : List Bracket → Nat → Nat
  | [], _ => 0
  | b :: bs, x => b.rate * slice x b + taxBp bs x

def WellFormed (bs : List Bracket) : Prop := ∀ b ∈ bs, b.lo ≤ b.hi

theorem slice_mono (b : Bracket) (hb : b.lo ≤ b.hi) {x y : Nat} (h : x ≤ y) : slice x b ≤ slice y b := by
  unfold slice
  simp only [Nat.min_def]
  split <;> split <;> split <;> split <;> omega

theorem taxBp_mono (bs : List Bracket) (hw : WellFormed bs) {x y : Nat} (h : x ≤ y) : taxBp bs x ≤ taxBp bs y := by
  induction bs with
  | nil => simp [taxBp]
  | cons b bs ih =>
    simp only [taxBp]
    have hb : b.lo ≤ b.hi := hw b (List.mem_cons_self ..)
    have hs := Nat.mul_le_mul_left b.rate (slice_mono b hb h)
    have hr := ih (fun c hc => hw c (List.mem_cons_of_mem _ hc))
    omega

/-- A whole schedule: brackets, a tax-free allowance that may shrink as income grows (as the UK's does),
and a rebate taken off the tax (as South Africa's is). -/
structure Schedule where
  brackets : List Bracket
  allowance : Nat → Nat
  rebate : Nat

/-- Income left after the allowance never falls as income rises: true when the allowance is fixed or shrinks. -/
def TaxableMono (s : Schedule) : Prop := ∀ x y, x ≤ y → x - s.allowance x ≤ y - s.allowance y

def tax (s : Schedule) (x : Nat) : Nat := taxBp s.brackets (x - s.allowance x) / 10000 - s.rebate

/-- **#7** More income never means less tax. -/
theorem tax_mono (s : Schedule) (hw : WellFormed s.brackets) (ha : TaxableMono s) {x y : Nat} (h : x ≤ y) :
    tax s x ≤ tax s y := by
  unfold tax
  have := Nat.div_le_div_right (c := 10000) (taxBp_mono s.brackets hw (ha x y h))
  omega

/-- **#7** The tax on a gain stacked on top of other income (tax with it, less tax without) is never negative. -/
theorem stacked_nonneg (s : Schedule) (hw : WellFormed s.brackets) (ha : TaxableMono s) (income gain : Nat) :
    tax s income ≤ tax s (income + gain) :=
  tax_mono s hw ha (Nat.le_add_right _ _)

/-- A fixed allowance always qualifies. -/
theorem fixed_allowance_mono (brackets : List Bracket) (a rebate : Nat) :
    TaxableMono ⟨brackets, fun _ => a, rebate⟩ := by
  intro x y h; simp; omega

/-- The UK taper qualifies: an allowance cut by £1 for every £2 over a threshold (never below zero). -/
theorem taper_allowance_mono (brackets : List Bracket) (pa limit rebate : Nat) :
    TaxableMono ⟨brackets, fun x => pa - (x - limit) / 2, rebate⟩ := by
  intro x y h
  simp only
  have : (x - limit) / 2 ≤ (y - limit) / 2 := Nat.div_le_div_right (by omega)
  omega

end Kanon.Brackets
