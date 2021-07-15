./analysis/constraints.csv: ./analysis/measure_constraints.zsh
	zsh $< | tee $@

fit_constraint_model: ./analysis/model_constraints.R ./analysis/constraints.csv
	Rscript $<

analyze_sizes: ./analysis/cost.sage
	sage $<
