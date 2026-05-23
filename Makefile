FINAL_RH_MODULE ?= TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction
RH_MATHLIB_DISCHARGE_MODULE ?= TauLib.BookIII.Bridge.RHMathlibDischarge
LANE_A_AXIOM_LEDGER_MODULE ?= TauLib.BookIII.Bridge.G8LaneAAxiomLedger
FULL_RH_AXIOM_LEDGER_MODULE ?= TauLib.BookIII.Bridge.G8FullRHSpineAxiomLedger
FINE_RH_AXIOM_LEDGER_MODULE ?= TauLib.BookIII.Bridge.G8FineRHSpineAxiomLedger

.PHONY: final-rh-spine final-rh-spine-axiomfree rh-mathlib-discharge rh-mathlib-discharge-axiomfree lane-a-axiom-ledger full-rh-axiom-ledger fine-rh-axiom-ledger

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

lane-a-axiom-ledger:
	lake build $(LANE_A_AXIOM_LEDGER_MODULE)
	python3 scripts/check_final_rh_spine_closure.py \
		--module $(LANE_A_AXIOM_LEDGER_MODULE) \
		--expected-axioms 1 \
		--expected-sorry 0

full-rh-axiom-ledger:
	lake build $(FULL_RH_AXIOM_LEDGER_MODULE)
	python3 scripts/check_final_rh_spine_closure.py \
		--module $(FULL_RH_AXIOM_LEDGER_MODULE) \
		--expected-axioms 2 \
		--expected-sorry 0

fine-rh-axiom-ledger:
	lake build $(FINE_RH_AXIOM_LEDGER_MODULE)
	python3 scripts/check_final_rh_spine_closure.py \
		--module $(FINE_RH_AXIOM_LEDGER_MODULE) \
		--expected-axioms 3 \
		--expected-sorry 0
