library(tidyverse)
library(ggpubr)
library(stringr)
library(scales)

d <- read_csv("data.csv")

print(d)

sum_d <- d %>%
    group_by(pf, log2n, n) %>%
    summarise(pf_time=mean(pf_wall_time),
              pf_size=mean(pf_size),
              ver_time=mean(ver_wall_time))
print(sum_d)

xlog2 <- scale_x_continuous(trans = log2_trans(),
                           breaks = trans_breaks("log2", function(x) 2^x),
                           labels = trans_format("log2", math_format(2^.x)))
ylog2 <- scale_y_continuous(trans = log2_trans(),
                           breaks = trans_breaks("log2", function(x) 2^x),
                           labels = trans_format("log2", math_format(2^.x)))

ggarrange(
    ggplot(sum_d, aes(x=n, y=pf_size, color=pf, shape=pf)) +
        geom_point() +
        xlog2 +
        labs(x = "IPA Size",
             y = "Proof Size (elements)",
             title = "Proof Size",
             color = "Protocol",
             shape = "Protocol"
             ),
    ggplot(sum_d, aes(x=n, y=pf_time, color=pf, shape=pf)) +
        geom_point() +
        xlog2 +
        ylog2 +
        labs(x = "IPA Size",
             y = "Proving Time (s)",
             title = "Proving Time",
             color = "Protocol",
             shape = "Protocol"
             ),
    ggplot(sum_d, aes(x=n, y=ver_time, color=pf, shape=pf)) +
        geom_point() +
        xlog2 +
        ylog2 +
        labs(x = "IPA Size",
             y = "Verification Time (s)",
             title = "Verification Time",
             color = "Protocol",
             shape = "Protocol"
             ),
    ncol=3,
    nrow=1,
    common.legend=TRUE,
    legend="right")
ggsave("main_plot.pdf", units = "in", width = 6, height = 3)
