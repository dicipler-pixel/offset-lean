import OperatorFirst.Offset

/-!
# Which identity sector?
Finite free-fermion occupation-basis algebra for the offset/cosmological-constant
motivation. This is not a gravitational action or a no-go theorem for emergence.
The one-particle identity lifts to particle number, not the Fock-space identity.
A common shift of all many-body energies instead cancels in normalization.
-/
noncomputable section
open scoped BigOperators
namespace OperatorFirst.Offset

def configurationEnergy {n : ℕ} (e : Fin n → ℝ) (b : Fin n → Bool) : ℝ :=
  ∑ i, if b i then e i else 0

def particleNumber {n : ℕ} (b : Fin n → Bool) : ℝ :=
  ∑ i, if b i then 1 else 0

/-- dGamma(K+k I)=dGamma(K)+k N in the eigenmode occupation basis. -/
theorem uniform_single_particle_shift {n : ℕ}
    (e : Fin n → ℝ) (b : Fin n → Bool) (k : ℝ) :
    configurationEnergy (fun i => e i + k) b =
      configurationEnergy e b + k * particleNumber b := by
  unfold configurationEnergy particleNumber
  calc
    (∑ i, if b i then e i + k else 0) =
        ∑ i, ((if b i then e i else 0) + k * (if b i then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : b i <;> simp [h]
    _ = (∑ i, if b i then e i else 0) + k * (∑ i, if b i then 1 else 0) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem empty_configuration_energy {n : ℕ} (e : Fin n → ℝ) :
    configurationEnergy e (fun _ => false) = 0 := by
  simp [configurationEnergy]

theorem identity_configuration_energy {n : ℕ} (b : Fin n → Bool) :
    configurationEnergy (fun _ => (1 : ℝ)) b = particleNumber b := by
  rfl

theorem identity_full_energy (n : ℕ) :
    configurationEnergy (fun _ : Fin n => (1 : ℝ)) (fun _ => true) = n := by
  simp [configurationEnergy]

/-- Vacuum and full occupation distinguish this operator from a Fock identity. -/
theorem identity_is_not_fock_constant :
    configurationEnergy (fun _ : Fin 2 => (1 : ℝ)) (fun _ => false) = 0 ∧
    configurationEnergy (fun _ : Fin 2 => (1 : ℝ)) (fun _ => true) = 2 := by
  constructor
  · exact empty_configuration_energy _
  · exact identity_full_energy 2

def partition {ι : Type*} [Fintype ι] (E : ι → ℝ) : ℝ :=
  ∑ i, Real.exp (-E i)

theorem partition_shift {ι : Type*} [Fintype ι] (E : ι → ℝ) (c : ℝ) :
    partition (fun i => E i + c) = Real.exp (-c) * partition E := by
  unfold partition
  simp_rw [neg_add, Real.exp_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A common MANY-BODY energy shift is removed by normalization. -/
theorem normalized_manybody_shift {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (c : ℝ) (i : ι) (hZ : partition E ≠ 0) :
    Real.exp (-(E i + c)) / partition (fun j => E j + c) =
      Real.exp (-E i) / partition E := by
  rw [partition_shift, neg_add, Real.exp_add]
  have hc : Real.exp (-c) ≠ 0 := Real.exp_ne_zero _
  field_simp [hc, hZ] <;> ring

/-- Positive rescaling preserves the negative-energy selection in a fixed
spectral basis; recovering a dimensional energy scale needs further data. -/
theorem negative_spectral_selection_rescale {s : ℝ} (hs : 0 < s) (e : ℝ) :
    s * e < 0 ↔ e < 0 := by
  constructor
  · intro h
    by_contra hn
    have he : 0 ≤ e := le_of_not_gt hn
    have hp : 0 ≤ s * e := mul_nonneg (le_of_lt hs) he
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hs h

end OperatorFirst.Offset

#print axioms OperatorFirst.Offset.uniform_single_particle_shift
#print axioms OperatorFirst.Offset.empty_configuration_energy
#print axioms OperatorFirst.Offset.identity_configuration_energy
#print axioms OperatorFirst.Offset.identity_full_energy
#print axioms OperatorFirst.Offset.identity_is_not_fock_constant
#print axioms OperatorFirst.Offset.partition_shift
#print axioms OperatorFirst.Offset.normalized_manybody_shift
#print axioms OperatorFirst.Offset.negative_spectral_selection_rescale
