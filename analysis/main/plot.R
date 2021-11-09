library(tidyverse)

d <- read_csv("data.csv")

print(d)

sum_d <- d %>%
    group_by(pf_system, log2n, n) %>%
    summarise(pf_time=mean(pf_time),
              pf_size=mean(pf_size),
              ver_time=mean(ver_time))
print(sum_d)

ggplot(sum_d, aes(x=n, y=pf_size, color=pf_system)) +
    geom_point() +
    scale_x_continuous(trans="log2") +
    labs(x = "IPA Size",
         y = "Proof Size (elements)",
         title = "Proof Sizes"
         ) +
    ggsave("pf_size.pdf", units = "in", width = 4, height = 3)

ggplot(sum_d, aes(x=n, y=pf_time, color=pf_system)) +
    geom_point() +
    scale_x_continuous(trans="log2") +
    scale_y_continuous(trans="log2") +
    labs(x = "IPA Size",
         y = "Proving Time (s)",
         title = "Proving Times"
         ) +
    ggsave("pf_time.pdf", units = "in", width = 4, height = 3)

ggplot(sum_d, aes(x=n, y=ver_time, color=pf_system)) +
    geom_point() +
    scale_x_continuous(trans="log2") +
    scale_y_continuous(trans="log2") +
    labs(x = "IPA Size",
         y = "Verification Time (s)",
         title = "Verification Times"
         ) +
    ggsave("ver_time.pdf", units = "in", width = 4, height = 3)
