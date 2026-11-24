import Foundations.Tensors.Semicontinuity.ZariskiSublevel

def S_NNN_18 : Prop :=
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ ((139999 : ℝ) / 100000)
