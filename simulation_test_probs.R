# Load required libraries
library(MASS)
library(stats)
library(numDeriv)
library(ks)
library(mvtnorm)
library(mltools)
library(data.table)

# Choose 1-Specificity level
t=0.1

mu_case <- c(1,1.1) # mu_case under the null hypothesis
#mu_case <- c(1, 1.5) # mu_case under alternative hypothesis
#mu_case <- c(0.8,2) # mu_case under alternative hypothesis
mu_control <- c(0,0) # mu_control 

# Variance-covariance matrix
sigma <- diag(1, nrow=2) 
sigma[outer(1:2, 1:2, function(i,j) i!=j)] <- 0.2
roc_full <- 1-pnorm(-sqrt(t(mu_case-mu_control)%*%solve(sigma)%*%(mu_case-mu_control))+qnorm(1-t))
roc_rest <- 1-pnorm(-sqrt(t(mu_case[-2]-mu_control[-2])%*%solve(sigma[1,1])%*%(mu_case[-2]-mu_control[2]))+qnorm(1-t))
delta <- roc_full-roc_rest # True difference in ROC under the null hypothesis


rho <- 1/3 # proportion of cases
N <- 600 # Total number of individuals
#S <- 1000


# Estimate standard deviation of the difference in ROC's
sd_est <- function(X_case, X_control, n_case, n_control, If, Ir,beta_est_full,
       beta_est_rest,rho){
  Sigma1 <- as.numeric(var(as.numeric(X_case%*%beta_est_full[-1] >= quantile(X_control%*%beta_est_full[-1], 1-t))-
  as.numeric(X_case[,-2]*beta_est_rest[-1] >= quantile(X_control[,-2]*beta_est_rest[-1], 1-t))))

surv_func_full <- function(beta){
  mean(X_case%*%beta >= quantile(X_control%*%beta, 1-t))
}

surv_func_rest <- function(beta){
  mean(X_case[,-2]*beta >= quantile(X_control[,-2]*beta, 1-t))
}
Sigma21 <- as.numeric(t(grad(surv_func_full,beta_est_full[-1]))%*%If[-1,-1]%*%grad(surv_func_full,beta_est_full[-1]))
Sigma22 <- as.numeric(t(grad(surv_func_rest,beta_est_rest[-1]))*Ir[-1,-1]*grad(surv_func_rest,beta_est_rest[-1]))

B1 <- (rho/(1+rho))*t(sapply(1:nrow(X_case), function(i) X_case[i,]/(1+rho*exp(X_case%*%beta_est_full[-1]))[i]))
B2 <- (1/(1+rho))*t(sapply(1:nrow(X_control), function(i) (X_control[i,]*rho*exp(X_control%*%beta_est_full[-1])[i])/(1+rho*exp(X_control%*%beta_est_full[-1]))[i]))

B3 <- (rho/(1+rho))*(sapply(1:nrow(X_case), function(i) X_case[i,-2]/(1+rho*exp(X_case[,-2]*beta_est_rest[-1]))[i]))
B4 <- (1/(1+rho))*(sapply(1:nrow(X_control), function(i) (X_control[i,-2]*rho*exp(X_control[,-2]*beta_est_rest[-1])[i])/(1+rho*exp(X_control[,-2]*beta_est_rest[-1]))[i]))
Sigma23 <- as.numeric(t(grad(surv_func_full,beta_est_full[-1]))%*%If[-1,-1]%*%
  (cov(B1,B3)/n_case+cov(B2,B4)/n_control)*Ir[-1,-1]*t(grad(surv_func_rest,beta_est_rest[-1])))


Sigma2 <- Sigma21+Sigma22+2*Sigma23

Sigma12 <- as.numeric(cov(as.numeric(X_case%*%beta_est_full[-1] >= quantile(X_control%*%beta_est_full[-1], 1-t))-
        as.numeric(X_case[,-2]*beta_est_rest[-1] >= quantile(X_control[,-2]*beta_est_rest[-1], 1-t)),
        as.numeric(t(grad(surv_func_full,beta_est_full[-1]))%*%If[-1,-1]%*%t(B1)-
          t(grad(surv_func_rest,beta_est_rest[-1]))*Ir[-1,-1]*as.vector(B3))))

SigmaD1 <- Sigma1+Sigma2+2*Sigma12

d1 <- kde(as.numeric(X_control%*%beta_est_full[-1]),
          eval.points = quantile(X_control%*%beta_est_full[-1], 1-t))
d2 <- kde(as.numeric(X_control[,-2]*beta_est_rest[-1]),
          eval.points = quantile(X_control[,-2]*beta_est_rest[-1], 1-t))
d3 <- empirical_cdf(data.table(x=as.numeric(X_control%*%beta_est_full[-1]), y=as.numeric(X_control[,-2]*beta_est_rest[-1])),data.table(x=quantile(X_control%*%beta_est_full[-1], 1-t), y= quantile(X_control[,-2]*beta_est_rest[-1], 1-t))
                                                )

quant_full <- function(beta){
  quantile(X_control%*%beta, 1-t)
}

quant_rest <- function(beta){
  quantile(X_control[,-2]*beta, 1-t)
}

B <- 200
bootstrap_means_full <- numeric(B)
bootstrap_means_rest <- numeric(B)
bootstrap_quantiles_full <- numeric(B)
bootstrap_quantiles_rest <- numeric(B)

for (j in 1:B) {
  sample_row_case <- sample(1:nrow(X_case%*%beta_est_full[-1]), replace = TRUE)
  sample_row_con <- sample(1:nrow(X_control%*%beta_est_full[-1]), replace = TRUE)
  B1_boot <- (rho/(1+rho))*t(sapply(sample_row_case, function(i) X_case[i,]/(1+rho*exp(X_case%*%beta_est_full[-1]))[i]))
  B2_boot <- (1/(1+rho))*t(sapply(sample_row_con, function(i) (X_control[i,]*rho*exp(X_control%*%beta_est_full[-1])[i])/(1+rho*exp(X_control%*%beta_est_full[-1]))[i]))
  B3_boot <- (rho/(1+rho))*(sapply(sample_row_case, function(i) X_case[i,-2]/(1+rho*exp(X_case[,-2]*beta_est_rest[-1]))[i]))
  B4_boot <- (1/(1+rho))*(sapply(sample_row_con, function(i) (X_control[i,-2]*rho*exp(X_control[,-2]*beta_est_rest[-1])[i])/(1+rho*exp(X_control[,-2]*beta_est_rest[-1]))[i]))
  bootstrap_means_full[j] <- as.numeric(t(grad(quant_full,beta_est_full[-1]))%*%If[-1,-1]%*%(rowMeans(t(B1_boot))-rowMeans(t(B2_boot))))
  bootstrap_means_rest[j] <- t(grad(quant_rest,beta_est_rest[-1]))*Ir[-1,-1]*(rowMeans(t(B3_boot))-rowMeans(t(B4_boot)))
  bootstrap_quantiles_full[j] <- quantile(X_control[sample_row_con,]%*%beta_est_full[-1], 1-t)
  bootstrap_quantiles_rest[j] <- quantile(X_control[sample_row_con,-2]*beta_est_rest[-1], 1-t)
}

Sigma3 <- as.numeric((t*(1-t))/(d1$estimate)^2+
  t(grad(quant_full,beta_est_full[-1]))%*%If[-1,-1]%*%grad(quant_full,beta_est_full[-1])-
  2*cov(bootstrap_means_full, bootstrap_quantiles_full))

Sigma4 <-  as.numeric((t*(1-t))/(d2$estimate)^2+
  t(grad(quant_rest,beta_est_rest[-1]))*Ir[-1,-1]*grad(quant_rest,beta_est_rest[-1])-
  2*cov(bootstrap_means_rest, bootstrap_quantiles_rest))

Sigma34 <- as.numeric((d3$CDF-(1-t)^2)/((d1$estimate)*
                               (d2$estimate)) +
             cov(bootstrap_means_full, bootstrap_means_rest)
           -cov(bootstrap_means_full, bootstrap_quantiles_rest)-
             cov(bootstrap_means_rest, bootstrap_quantiles_full))

d4 <- kde(as.numeric(X_case%*%beta_est_full[-1]),
    eval.points = quantile(X_control%*%beta_est_full[-1], 1-t))

d5 <- kde(as.numeric(X_case[,-2]*beta_est_rest[-1]), 
          eval.points= quantile(X_control[,-2]*beta_est_rest[-1], 1-t))
SigmaD0 <- as.numeric(t(c(-(d4$estimate),(d5$estimate)))%*%
  matrix(c(Sigma3, Sigma34, Sigma34, Sigma4),nrow=2)%*%
  c(-(d4$estimate),(d5$estimate)))
M1 <- numeric(0)
M2 <- numeric(0)

for (j in 1:B) {
  sample_row_case <- sample(1:nrow(X_case%*%beta_est_full[-1]), replace = TRUE)
  sample_row_con <- sample(1:nrow(X_control%*%beta_est_full[-1]), replace = TRUE)
  B1_boot <- (rho/(1+rho))*t(sapply(sample_row_case, function(i) X_case[i,]/(1+rho*exp(X_case%*%beta_est_full[-1]))[i]))
  B2_boot <- (1/(1+rho))*t(sapply(sample_row_con, function(i) (X_control[i,]*rho*exp(X_control%*%beta_est_full[-1])[i])/(1+rho*exp(X_control%*%beta_est_full[-1]))[i]))
  B3_boot <- (rho/(1+rho))*(sapply(sample_row_case, function(i) X_case[i,-2]/(1+rho*exp(X_case[,-2]*beta_est_rest[-1]))[i]))
  B4_boot <- (1/(1+rho))*(sapply(sample_row_con, function(i) (X_control[i,-2]*rho*exp(X_control[,-2]*beta_est_rest[-1])[i])/(1+rho*exp(X_control[,-2]*beta_est_rest[-1]))[i]))
  M1[j] <- mean(as.numeric(X_case%*%beta_est_full[-1] >= quantile(X_control[sample_row_con,]%*%beta_est_full[-1], 1-t))-
                  as.numeric(X_case[,-2]*beta_est_rest[-1] >= quantile(X_control[sample_row_con,-2]*beta_est_rest[-1], 1-t)))-
      as.numeric(mean(t(grad(surv_func_full,beta_est_full[-1]))%*%If[-1,-1]%*%t(B1_boot)+
                        t(grad(surv_func_rest,beta_est_rest[-1]))*Ir[-1,-1]*(B3_boot))+
                   mean(t(grad(surv_func_full,beta_est_full[-1]))%*%If[-1,-1]%*%t(B2_boot)-
                          t(grad(surv_func_rest,beta_est_rest[-1]))*Ir[-1,-1]*(B4_boot)))
   M2[j] <- mean((X_case[sample_row_case,]%*%beta_est_full[-1] >= quantile(X_control%*%beta_est_full[-1], 1-t))-
                  (X_case[sample_row_case,-2]*beta_est_rest[-1] >= quantile(X_control[,-2]*beta_est_rest[-1], 1-t)))
}
return(sqrt(SigmaD1/n_case + SigmaD0/n_control+2*cov(M1,M2)))
}

# Function to conduct the sequential test 
hyp_test <- function(t, mu_case, mu_control, delta, rho,N){
  case_con_ind <- c(rep(1,N*rho), rep(0,N*(1-rho)))
  # Generate data
  X <- matrix(0,nrow = N,ncol = 2)
  for (i in 1:N) {
    if(case_con_ind[i]==1){
      X[i,] <- rmvnorm(1, mu_case, sigma)
    }
    else{
      X[i,] <- rmvnorm(1, mu_control, sigma) 
    }
  }
  X_case <- X[which(case_con_ind==1),]
  X_control <- X[which(case_con_ind==0),]
  N_case <- nrow(X_case)
  N_control <- nrow(X_control)
  beta <- solve(sigma)%*%(mu_case-mu_control)
  smp_size_case_s1 <- floor(0.5 * nrow(X_case))
  smp_size_control_s1 <- floor(0.5 * nrow(X_control))
  s1_ind_case <- sample(seq_len(nrow(X_case)), size = smp_size_case_s1)
  s1_ind_control <- sample(seq_len(nrow(X_control)), size = smp_size_control_s1)
  X_case_s1 <- X_case[s1_ind_case, ]
  X_case_s2 <- X_case[-s1_ind_case, ]
  X_control_s1 <- X_control[s1_ind_control, ]
  X_control_s2 <- X_control[-s1_ind_control, ]
  n_case <- nrow(X_case_s1)
  n_control <- nrow(X_control_s1)
  Y <- c(rep(1,nrow(X_case_s1)),rep(0,nrow(X_control_s1)))
  model_full <- glm(Y~rbind(X_case_s1,X_control_s1),family = binomial, control = list(maxit=100))
  beta_est_full <- model_full$coefficients
  roc_full_est <- mean(X_case_s1%*%beta_est_full[-1] >= quantile(X_control_s1%*%beta_est_full[-1], 1-t))
  model_rest <- glm(Y~c(X_case_s1[,-2],X_control_s1[,-2]),family = binomial, control = list(maxit=100))
  beta_est_rest <- model_rest$coefficients
  roc_rest_est <- mean(X_case_s1[,-2]*beta_est_rest[-1] >= quantile(X_control_s1[,-2]*beta_est_rest[-1], 1-t))
  delta_est <- roc_full_est - roc_rest_est
  If <- vcov(model_full) 
  Ir <- vcov(model_rest)
  sd_est1 <- sd_est(X_case_s1, X_control_s1, n_case, n_control, If, Ir,beta_est_full,
                   beta_est_rest,rho)
  test_stat <- (delta_est-round(delta,2))/sd_est1
 if(test_stat <0){ #Replace 0 by 0.76 for Pocock boundary
   C= -1
 } 
  else if(test_stat> 2.36){ #Replace 2.36 by 1.83 for Pocock boundary
    C=0
  } else{C=1}
  C2=0
  if(C==1){
    Y <- c(rep(1,nrow(X_case)),rep(0,nrow(X_control)))
    model_full <- glm(Y~rbind(X_case,X_control),family = binomial, control = list(maxit=100))
    beta_est_full <- model_full$coefficients
    roc_full_est <- mean(X_case%*%beta_est_full[-1] >= quantile(X_control%*%beta_est_full[-1], 1-t))
    model_rest <- glm(Y~c(X_case[,-2],X_control[,-2]),family = binomial, control = list(maxit=100))
    beta_est_rest <- model_rest$coefficients
    roc_rest_est <- mean(X_case[,-2]*beta_est_rest[-1] >= quantile(X_control[,-2]*beta_est_rest[-1], 1-t))
    delta_est2 <- roc_full_est - roc_rest_est
    If <- vcov(model_full)
    Ir <- vcov(model_rest)
    sd_est2 <- sd_est(X_case, X_control, N_case, N_control,If, Ir,beta_est_full,
                     beta_est_rest,rho)
    test_stat2 <- (delta_est2-round(delta,2))/sd_est2
    if(test_stat2 <1.67){C2=-1} #Replace 1.67 by 1.83 for Pocock boundary
    else{C2=2}
  }
  return(c(C,C2))
}

S=10 # Number of Monte Carlo simulations

out1 <- replicate(S,hyp_test(t,mu_case,mu_control,delta, rho,N)) # Obtaining probabilities under the null
#out1 <- hyp_test(t,c(1,1.5),mu_control,delta, rho,N) # Obtaining probabilities under the alternatives
#out1 <- hyp_test(t,c(0.8,2),mu_control,delta, rho,N) # Obtaining probabilities under the alternatives

reject_s1 <- mean(out1[1,]==0)  
se_reject_s1 <- sqrt((reject_s1*(1-reject_s1))/S)
next_s1 <- mean(out1[1,]==1) 
se_next_s1 <- sqrt((next_s1*(1-next_s1))/S)
accept_s2 <- sum(out[2,]==-1)/sum(out[1,]==1)
reject_s2 <- sum(out[2,]==2)/sum(out[1,]==1)
reject_s2 <- mean((out1[1,]==1)*(out1[2,]==2))
se_reject_s2 <- sqrt((reject_s2*(1-reject_s2))/S)
reject_prop <- (sum(out1[1,]==0)+sum((out1[1,]==1)*(out1[2,]==2)))/S
se_reject_prop <- sqrt((mean(out1[1,]==0)*(1-mean(out1[1,]==0))+mean((out1[1,]==1)*(out1[2,]==2))*
  (1-mean((out1[1,]==1)*(out1[2,]==2)))-2*mean(out1[1,]==0)*mean((out1[1,]==1)*(out1[2,]==2)))/S)

res1 <- c(reject_s1, se_reject_s1, next_s1, se_next_s1, reject_s2, se_reject_s2, reject_prop, se_reject_prop)
res1 
