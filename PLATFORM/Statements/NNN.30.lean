import Foundations.Tensors.Semicontinuity.ZariskiSublevel

/-- The unconditional cube bound obtained from the nine-quarters bound for matrix multiplication. -/
def S_NNN_30 : Prop :=
  ∀ (n : ℕ+) (T : Semicontinuity.KTensor ℂ (fun _ : Fin 3 => n)),
    Semicontinuity.asympRank T ≤ ((n : ℕ) : ℝ) ^ (3 * Real.sqrt 3 / 4)
