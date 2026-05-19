FINAL_RH_MODULE ?= TauLib.BookIII.Bridge.G8BookIIICharacterAcceptedRealizationReduction

.PHONY: final-rh-spine final-rh-spine-axiomfree

final-rh-spine: final-rh-spine-axiomfree

final-rh-spine-axiomfree:
	lake build $(FINAL_RH_MODULE)
	python3 scripts/check_final_rh_spine_closure.py \
		--module $(FINAL_RH_MODULE) \
		--expected-axioms 0 \
		--expected-sorry 0
