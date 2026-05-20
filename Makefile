FINAL_RH_MODULE ?= TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction
RH_MATHLIB_DISCHARGE_MODULE ?= TauLib.BookIII.Bridge.RHMathlibDischarge

.PHONY: final-rh-spine final-rh-spine-axiomfree rh-mathlib-discharge rh-mathlib-discharge-axiomfree

final-rh-spine: final-rh-spine-axiomfree

final-rh-spine-axiomfree:
	lake build $(FINAL_RH_MODULE)
	python3 scripts/check_final_rh_spine_closure.py \
		--module $(FINAL_RH_MODULE) \
		--expected-axioms 0 \
		--expected-sorry 0

rh-mathlib-discharge:
	lake env lean TauLib/BookIII/Bridge/RHMathlibDischarge.lean
	lake build $(RH_MATHLIB_DISCHARGE_MODULE)

rh-mathlib-discharge-axiomfree: rh-mathlib-discharge
	python3 scripts/check_final_rh_spine_closure.py \
		--module $(RH_MATHLIB_DISCHARGE_MODULE) \
		--expected-axioms 0 \
		--expected-sorry 0
