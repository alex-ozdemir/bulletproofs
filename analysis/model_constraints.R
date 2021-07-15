library(tidyverse)
d <- read_csv("analysis/constraints.csv") %>% filter(k > 20) %>% mutate(k_by_log2k = k / log2(k))
fit <- lm(cs~k+m+k_by_log2k, data=d)
summary(fit)
