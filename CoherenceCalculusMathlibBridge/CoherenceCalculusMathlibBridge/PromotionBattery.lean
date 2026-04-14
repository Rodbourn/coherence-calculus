import CoherenceCalculusMathlibBridge.AbstractHilbert

namespace CoherenceCalculusMathlibBridge

open CoherenceCalculus

theorem promotedObservedLaw_unfold
    {Observed Ambient : Type _}
    (ctx : PromotedConstitutiveContext Observed Ambient)
    (p : Observed) :
    promotedObservedLaw ctx p =
      ctx.combine
        (ctx.project (ctx.transport (ctx.reconstruct p)))
        (PromotedConstitutiveTerm ctx p) := by
  rfl

theorem fiberedPromotedObservedLaw_unfold
    {Observed Ambient : Type _}
    (ctx : FiberedPromotedConstitutiveContext Observed Ambient)
    (p : Observed) :
    fiberedPromotedObservedLaw ctx p =
      ctx.combine p
        (ctx.project p (ctx.transport p (ctx.reconstruct p)))
        (FiberedPromotedConstitutiveTerm ctx p) := by
  rfl

theorem AbstractPromotionModel.characteristic_exact
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    characteristic_scale_promotion model.context model.characteristic = model.characteristic := by
  rfl

theorem AbstractPromotionModel.admissible_exact
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    admissible_promotion model.admissible = model.admissible := by
  rfl

theorem AbstractPromotionModel.toPromotionContract_context
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    model.toPromotionContract.context = model.context := by
  rfl

theorem AbstractPromotionModel.toPromotionContract_characteristic
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    model.toPromotionContract.characteristic = model.characteristic := by
  rfl

theorem AbstractPromotionModel.toPromotionContract_admissible
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    model.toPromotionContract.admissible = model.admissible := by
  rfl

theorem AbstractPromotionModel.toPromotionContract_minimumEnergy
    {Observed Ambient Law : Type _}
    (model : AbstractPromotionModel Observed Ambient Law) :
    model.toPromotionContract.minimumEnergy = model.minimumEnergy := by
  rfl

theorem AbstractFiberedPromotionModel.characteristic_exact
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    fibered_characteristic_scale_promotion model.context model.characteristic =
      model.characteristic := by
  rfl

theorem AbstractFiberedPromotionModel.admissible_exact
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    fibered_admissible_promotion model.admissible = model.admissible := by
  rfl

theorem AbstractFiberedPromotionModel.toFiberedPromotionContract_context
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    model.toFiberedPromotionContract.context = model.context := by
  rfl

theorem AbstractFiberedPromotionModel.toFiberedPromotionContract_characteristic
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    model.toFiberedPromotionContract.characteristic = model.characteristic := by
  rfl

theorem AbstractFiberedPromotionModel.toFiberedPromotionContract_admissible
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    model.toFiberedPromotionContract.admissible = model.admissible := by
  rfl

theorem AbstractFiberedPromotionModel.toFiberedPromotionContract_minimumEnergy
    {Parameter Observed Ambient Law : Type _}
    (model : AbstractFiberedPromotionModel Parameter Observed Ambient Law) :
    model.toFiberedPromotionContract.minimumEnergy = model.minimumEnergy := by
  rfl

end CoherenceCalculusMathlibBridge
