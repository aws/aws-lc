# Plot data from IRQ duration table
#
# 1. create results-runtime-multi with analyze_options.sh:
#
# $ cat results-runtime-multi
# Number of bits  min entropy
# 10       0.406505
# 11       0.445082
# 12       0.402972
# 13       0.459021
# 14       0.436911
# 15       0.578995
# 16       0.643272
# 17       0.573532
# 18       0.627915
# 19       0.503923
# 20       0.720609
# 21       1.871527
# 22       2.491569
# 23       2.481533
# 24       2.493987
# 25       2.491303
# 26       2.495017
#
# 2. Generate plot: Rscript --vanilla draw_graph_analyze_options.r results-runtime-multi
#

args <- commandArgs(trailingOnly = TRUE)

if (length(args) != 1) {
	stop("Invoke with <input file>")
}

file <- args[1]

data <- read.csv(file=file, header=TRUE, sep="\t")

pdf("memory_access_times.pdf", width=8, height=5, pointsize=10)

# print software
plot(data[,1], data[,2], type="b", col="red", main="Memory Access Time Variations", pch=19, xlab="Memory size in powers of 2", ylab="SP800-90B Min Entropy", ylim=c(min(data[,2]), max(data[,2])))
