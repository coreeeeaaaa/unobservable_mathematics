reproduce:
	cd lean && lake build
	bash tools/proof_coverage.sh > proof_coverage.txt