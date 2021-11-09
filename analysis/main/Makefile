data.csv: ./run.zsh
	zsh $< | tee $@

pf_size.pdf: ./plot.R ./data.csv
	Rscript $<

pf_time.pdf: ./plot.R ./data.csv
	Rscript $<

ver_time.pdf: ./plot.R ./data.csv
	Rscript $<
