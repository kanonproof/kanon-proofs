/-!
# One year's rules can't change another year (#8)

The engines run year by year: each year uses only that year's rules, that year's events and what
was carried in (unused losses). We prove that changing the rules for one year never changes any
earlier year, and changes a later year only through what is carried forward.
-/

namespace Kanon.Years

variable {R E C T : Type}

/-- Year `n`'s result (tax, carried out), running every year from 0. -/
def run (step : R → List E → C → T × C) (rules : Nat → R) (events : Nat → List E) (start : C) : Nat → T × C
  | 0 => step (rules 0) (events 0) start
  | n + 1 => step (rules (n + 1)) (events (n + 1)) (run step rules events start n).2

/-- **#8** Rules changed from year `z` on leave every year before `z` exactly as it was. -/
theorem past_unchanged (step : R → List E → C → T × C) (rules rules' : Nat → R) (events : Nat → List E) (start : C)
    (z : Nat) (same : ∀ y, y < z → rules' y = rules y) :
    ∀ y, y < z → run step rules' events start y = run step rules events start y := by
  intro y
  induction y with
  | zero => intro h; simp [run, same 0 h]
  | succ n ih => intro h; simp [run, same (n + 1) h, ih (by omega)]

/-- **#8** A later year with the same rules and the same carried-in amount gives the same result:
another year's rules can only reach it through what's carried forward. -/
theorem only_through_carry (step : R → List E → C → T × C) (rules rules' : Nat → R) (events : Nat → List E) (start : C)
    (n : Nat) (sameRules : rules' (n + 1) = rules (n + 1))
    (sameCarry : (run step rules' events start n).2 = (run step rules events start n).2) :
    run step rules' events start (n + 1) = run step rules events start (n + 1) := by
  simp [run, sameRules, sameCarry]

/-- **#8** Events in one year never change an earlier year either. -/
theorem past_events_unchanged (step : R → List E → C → T × C) (rules : Nat → R) (events events' : Nat → List E) (start : C)
    (z : Nat) (same : ∀ y, y < z → events' y = events y) :
    ∀ y, y < z → run step rules events' start y = run step rules events start y := by
  intro y
  induction y with
  | zero => intro h; simp [run, same 0 h]
  | succ n ih => intro h; simp [run, same (n + 1) h, ih (by omega)]

end Kanon.Years
