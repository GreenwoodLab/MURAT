## Dec. 10, 2015
## use for package

Para_Match_Kur <- function( lambda ){
## get parameters for the mixture chisquare r.v., Q, and the approximated chisquare r.v., X.
## using moment matching, match the mean, variance, and the kurtosis

c <-rep(NA,4)
c[1] <- sum(lambda)
c[2] <- sum(lambda^2)
c[3] <- sum(lambda^3)
c[4] <- sum(lambda^4)
s1 <- c[3]/(c[2])^(3/2)
s2 <- c[4]/(c[2])^2
beta1 <- sqrt(8)*s1
beta2 <- 12*s2

mu.Q <- c[1]
sigma.Q <- sqrt(2*c[2])
skewness.Q <- beta1
kurtosis.Q <- beta2

df.X <- 12/kurtosis.Q
mu.X <- df.X
sigma.X <- sqrt( 2*df.X )

out <- list( mu.Q=mu.Q, sigma.Q=sigma.Q, skewness.Q=skewness.Q, kurtosis.Q=kurtosis.Q, df.X=df.X, mu.X=mu.X,sigma.X=sigma.X )
return(out)

}


Int_Fnc <-function( x, rho, q.min.rho, tau.rho, mu.kappa, var.kappa,mix.chi2.xi, mix.chi2.eta, eta_rv){

  mu.xi <- mix.chi2.xi$mu.Q
  sigma.xi <- mix.chi2.xi$sigma.Q

  delta.rho <- matrix( NA, nrow=length(rho), ncol=length(x) )
  for ( v in 1:length(rho) ){
   delta.rho[v,] <- ( q.min.rho[v] - tau.rho[v] * x ) / ( 1-rho[v] )
  }	
  
  
  df.xi.approx <- mix.chi2.xi$df.X
  mu.xi.approx <- mix.chi2.xi$mu.X
  sigma.xi.approx <- mix.chi2.xi$sigma.X

  delta.x.approx <- ( apply( delta.rho, 2, min ) - mu.kappa ) * ( sigma.xi.approx / sqrt(var.kappa) ) + mu.xi.approx


  ## P( \xi < delta.x ) = F_{\xi}( delta.x )
  F.xi.approx <- pchisq(delta.x.approx, df = df.xi.approx)

  F.xi <- F.xi.approx
  f.eta <- d( eta_rv  )(x)  ## to add function d_eta_func and F_eta_func ##  eta_rv = Eta_RV(eigen.value.eta)
  
  integrate.fnc <- (1 - F.xi) * f.eta
	
  return(integrate.fnc)
}



Optimal_PValue <- function(rho, q.min.rho, tau.rho, mu.kappa, var.kappa, mix.chi2.xi, mix.chi2.eta, eigen.value.eta ){

      mu.eta <- mix.chi2.eta$mu.Q
      sigma.eta <- mix.chi2.eta$sigma.Q
      df.eta.approx <- mix.chi2.eta$df.X
      mu.eta.approx <- mix.chi2.eta$mu.X
      sigma.eta.approx <- mix.chi2.eta$sigma.X

      eta_rv <- Eta_RV(eigen.value.eta) ##  to calculate Eta only once per calculation of Optimal_PValue(...) 

      lower <- 0
	# Jan 2, 2015: calculate x0 for g(x)
      x0 <- min( q.min.rho / tau.rho )
      upper <- x0 

      # Jan 2, 2015 to use relative error  
      int <- integrate( Int_Fnc, lower, upper, subdivisions=20000,
      rho=rho, q.min.rho=q.min.rho, tau.rho=tau.rho, mu.kappa=mu.kappa,
      var.kappa=var.kappa, mix.chi2.xi=mix.chi2.xi, mix.chi2.eta=mix.chi2.eta, eta_rv = eta_rv, rel.tol = 10^-2)
       
      p.value <- int$value + ( 1 -  p( eta_rv )(upper) )

      return( list(p = p.value,  abs.err = int$abs.error) )
}


### to define F_eta_func(upper, eigen.value.eta)  and d_eta_func(upper, eigen.value.eta))

Eta_RV <- function(eigen.value.eta) {
## added on jan 2, 2015
## to calculate cumulative distribution function of mixture of chi-squre using convolution approach 
## the name "eta" refers to the RV eta in the MURAT approach, but the function F_eta_func can be used for more general purpose

   ###  remove useless lamdas with absolute value less than  1e-10
   if ( sum(abs(eigen.value.eta) > 1e-10) == 0 ) 
	{ Eta <- DiscreteDistribution( supp = 0 , prob = 1 )  }  ## chi-square 0, with mass prob 1 at 0
   else { 
         lam <- sort(eigen.value.eta[abs(eigen.value.eta) > 1e-10], decreasing = TRUE) 
         Eta <- lam[1] *Chisq(df = 1)  
         if (length(lam) >=2) { for (j in (2: length(lam) ) ) {  Eta <-  Eta + lam[j]*Chisq(df = 1)  } }
        }
    return(Eta)
}

#### new gls_sun: from gls() in "nlme 2.1.134"
#### Jan 22, 2016 by JSUN XT
#### Edit 1:  stop(optRes$message) ==> numIter0 <- -999
#### Edit 2:  glsEstimate ==> nlme:::glsEstimate
#### Edit 3:  glsApVar  ==> nlme:::glsApVar
gls_sun <- 
  function (model, data = sys.frame(sys.parent()), correlation = NULL, 
            weights = NULL, subset, method = c("REML", "ML"), na.action = na.fail, 
            control = list(), verbose = FALSE) 
  {
    Call <- match.call()
    controlvals <- glsControl()
    if (!missing(control)) {
      controlvals[names(control)] <- control
    }
    if (!inherits(model, "formula") || length(model) != 3L) {
      stop("\nmodel must be a formula of the form \"resp ~ pred\"")
    }
    method <- match.arg(method)
    REML <- method == "REML"
    groups <- if (!is.null(correlation)) 
      getGroupsFormula(correlation)
    glsSt <- glsStruct(corStruct = correlation, varStruct = varFunc(weights))
    model <- terms(model, data = data)
    mfArgs <- list(formula = asOneFormula(formula(glsSt), model, 
                                          groups), data = data, na.action = na.action)
    if (!missing(subset)) {
      mfArgs[["subset"]] <- asOneSidedFormula(Call[["subset"]])[[2L]]
    }
    mfArgs$drop.unused.levels <- TRUE
    dataMod <- do.call(model.frame, mfArgs)
    origOrder <- row.names(dataMod)
    if (!is.null(groups)) {
      groups <- eval(parse(text = paste("~1", deparse(groups[[2L]]), 
                                        sep = "|")))
      grps <- getGroups(dataMod, groups, level = length(getGroupsFormula(groups, 
                                                                         asList = TRUE)))
      ord <- order(grps)
      grps <- grps[ord]
      dataMod <- dataMod[ord, , drop = FALSE]
      revOrder <- match(origOrder, row.names(dataMod))
    }
    else grps <- NULL
    X <- model.frame(model, dataMod)
    contr <- lapply(X, function(el) if (inherits(el, "factor")) 
      contrasts(el))
    contr <- contr[!unlist(lapply(contr, is.null))]
    X <- model.matrix(model, X)
    if (ncol(X) == 0L) 
      stop("no coefficients to fit")
    y <- eval(model[[2L]], dataMod)
    N <- nrow(X)
    p <- ncol(X)
    parAssign <- attr(X, "assign")
    fTerms <- terms(as.formula(model), data = data)
    namTerms <- attr(fTerms, "term.labels")
    if (attr(fTerms, "intercept") > 0) {
      namTerms <- c("(Intercept)", namTerms)
    }
    namTerms <- factor(parAssign, labels = namTerms)
    parAssign <- split(order(parAssign), namTerms)
    fixedSigma <- (controlvals$sigma > 0)
    attr(glsSt, "conLin") <- list(Xy = array(c(X, y), c(N, ncol(X) + 
                                                          1L), list(row.names(dataMod), c(colnames(X), deparse(model[[2]])))), 
                                  dims = list(N = N, p = p, REML = as.integer(REML)), logLik = 0, 
                                  sigma = controlvals$sigma, fixedSigma = fixedSigma)  
    glsEstControl <- controlvals["singular.ok"]
    glsSt <- Initialize(glsSt, dataMod, glsEstControl)
    parMap <- attr(glsSt, "pmap")
    numIter <- numIter0 <- 0L
    repeat {
      oldPars <- c(attr(glsSt, "glsFit")[["beta"]], coef(glsSt))
      if (length(coef(glsSt))) {
        optRes <- if (controlvals$opt == "nlminb") {
          nlminb(c(coef(glsSt)), function(glsPars) -logLik(glsSt, 
                                                           glsPars), control = list(trace = controlvals$msVerbose, 
                                                                                    iter.max = controlvals$msMaxIter))
        }
        else {
          optim(c(coef(glsSt)), function(glsPars) -logLik(glsSt, 
                                                          glsPars), method = controlvals$optimMethod, 
                control = list(trace = controlvals$msVerbose, 
                               maxit = controlvals$msMaxIter, reltol = if (numIter == 
                                                                             0L) controlvals$msTol else 100 * .Machine$double.eps))
        }
        coef(glsSt) <- optRes$par
      }
      else {
        optRes <- list(convergence = 0)
      }
      attr(glsSt, "glsFit") <- nlme::glsEstimate(glsSt, control = glsEstControl)
      if (!needUpdate(glsSt)) {
        if (optRes$convergence) 
          stop(optRes$message)
        break
      }
      numIter <- numIter + 1L
      glsSt <- update(glsSt, dataMod)
      aConv <- c(attr(glsSt, "glsFit")[["beta"]], coef(glsSt))
      conv <- abs((oldPars - aConv)/ifelse(aConv == 0, 1, aConv))
      aConv <- c(beta = max(conv[1:p]))
      conv <- conv[-(1:p)]
      for (i in names(glsSt)) {
        if (any(parMap[, i])) {
          aConv <- c(aConv, max(conv[parMap[, i]]))
          names(aConv)[length(aConv)] <- i
        }
      }
      if (verbose) {
        cat("\nIteration:", numIter)
        cat("\nObjective:", format(optRes$value), "\n")
        print(glsSt)
        cat("\nConvergence:\n")
        print(aConv)
      }
      if (max(aConv) <= controlvals$tolerance) {
        break
      }
      if (numIter > controlvals$maxIter) {
        stop("maximum number of iterations reached without convergence")
      }
    }
    glsFit <- attr(glsSt, "glsFit")
    namBeta <- names(glsFit$beta)
    attr(glsSt, "fixedSigma") <- fixedSigma
    attr(parAssign, "varBetaFact") <- varBeta <- glsFit$sigma * 
      glsFit$varBeta * sqrt((N - REML * p)/(N - p))
    varBeta <- crossprod(varBeta)
    dimnames(varBeta) <- list(namBeta, namBeta)
    Fitted <- fitted(glsSt)
    if (!is.null(grps)) {
      grps <- grps[revOrder]
      Fitted <- Fitted[revOrder]
      Resid <- y[revOrder] - Fitted
      attr(Resid, "std") <- glsFit$sigma/varWeights(glsSt)[revOrder]
    }
    else {
      Resid <- y - Fitted
      attr(Resid, "std") <- glsFit$sigma/varWeights(glsSt)
    }
    names(Resid) <- names(Fitted) <- origOrder
    apVar <- if (controlvals$apVar) 
      nlme::glsApVar(glsSt, glsFit$sigma, .relStep = controlvals[[".relStep"]], 
                      minAbsPar = controlvals[["minAbsParApVar"]], natural = controlvals[["natural"]])
    else "Approximate variance-covariance matrix not available"
    dims <- attr(glsSt, "conLin")[["dims"]]
    dims[["p"]] <- p
    attr(glsSt, "conLin") <- NULL
    attr(glsSt, "glsFit") <- NULL
    attr(glsSt, "fixedSigma") <- fixedSigma
    estOut <- list(modelStruct = glsSt, dims = dims, contrasts = contr, 
                   coefficients = glsFit[["beta"]], varBeta = varBeta, sigma = if (fixedSigma) controlvals$sigma else glsFit$sigma, 
                   apVar = apVar, logLik = glsFit$logLik, numIter = if (needUpdate(glsSt)) numIter else numIter0, 
                   groups = grps, call = Call, method = method, fitted = Fitted, 
                   residuals = Resid, parAssign = parAssign, na.action = attr(dataMod, 
                                                                              "na.action"))
    if (inherits(data, "groupedData")) {
      attr(estOut, "units") <- attr(data, "units")
      attr(estOut, "labels") <- attr(data, "labels")
    }
    attr(estOut, "namBetaFull") <- colnames(X)
    class(estOut) <- "gls"
    estOut
  }




##-----------------------------##
##      core function          ##
##-----------------------------##

MURAT <- function (Y, G, X, rho=seq(0,0.9,by=0.1), weight=FALSE, weight.para1=NA, weight.para2=NA ){
   # library(CompQuadForm)
   # library(nlme)
   # library("distr")

   X <- as.matrix(X)
   G <- as.matrix(G)
   Y <- as.matrix(Y) 

   n <-  dim(X)[1]
   p <-  dim(G)[2]
   m <-  dim(X)[2]
   K <-  dim(Y)[2]

   maf <- apply(G,2,mean)/2

   if (!weight) {W <- diag(p)
                     } else {  W <- diag( dbeta(maf, weight.para1, weight.para2)^2 , nrow=p, ncol=p )}

   ## standardize each column of Y
   Y.sd <- apply( Y, 2, scale )

   ## combine each column of Y into a vector
   Y.star <- matrix(c(t(Y.sd)),ncol=1)

   id <- kronecker( c(1:n), rep(1,K) )
   component <- rep( c(1:K), n )

   X.star <- matrix (NA, nrow=K*n, ncol=K*m)
   for (i in 1:n)
    {
      X.star[( (i-1)*K+1 ):( i*K ),] <- kronecker( diag(1,K), t(X[i,]) )
    }

   ###### fit null model ######
   fit.null <- gls_sun(Y.star ~ -1 + X.star,  
                correlation = corSymm(form = ~ 1 | id),
                weights = varIdent(form = ~ 1 | component)) ###, control=glsControl(msVerbose=TRUE))

   ## get residual, alpha.hat, Sigma.hat, and Sigma.e.hat 
   ## if   (fit.null$numIter == -999) {}  ## gls() converge fails  
   resid <- residuals( fit.null, type="response" )[ 1:(K*n) ]
   alpha.hat <- coef(fit.null)
   Sigma.hat <- getVarCov(fit.null)

   ###### some useful matrices ######

   inv.Sigma.hat <- solve(Sigma.hat) 

   ## inverse Sigma.hat.half
   eigen.inv.Sigma.hat <- eigen( inv.Sigma.hat, symmetric=TRUE )
   eigen.inv.Sigma.hat.value <- eigen.inv.Sigma.hat$values
   eigen.inv.Sigma.hat.vec <- eigen.inv.Sigma.hat$vector
   inv.Sigma.hat.half <- eigen.inv.Sigma.hat.vec %*% diag( sqrt(eigen.inv.Sigma.hat.value) ) %*% t(eigen.inv.Sigma.hat.vec)
   #inv.Sigma.hat.half <- eigen.inv.Sigma.hat.vec %*% ( sqrt(eigen.inv.Sigma.hat.value) * diag(K) ) %*% t(eigen.inv.Sigma.hat.vec)

   Z <- inv.Sigma.hat.half
   bar.z <- ( Z %*% rep(1,K) ) / K
   M <- ( bar.z %*% t(bar.z) ) / ( sum( bar.z^2 ) )

   P.x <- X %*% solve( t(X) %*% X ) %*% t(X)
   P.x.com <- diag(1,n) - P.x

   G.Pxcom.G <- (W^{1/2}) %*% t(G) %*% P.x.com %*% G %*% (W^{1/2})
   GGt <- G %*% W %*% t(G)

   ###### some useful eigenvalues that do not depend on rho ######

   ## part of for S_{\tau^2}(\rho)
   eigen.value.S.tau.part1 <- eigen( G.Pxcom.G, symmetric=TRUE )$values

   ## for \xi
   Mat1 <- G.Pxcom.G
   Mat2 <- t(Z) %*% ( diag(1,K) -M ) %*% Z 
   eigen.value.Mat1 <- eigen.value.S.tau.part1
   eigen.value.Mat2 <- eigen( Mat2, symmetric=TRUE )$values
   eigen.value.xi <- kronecker( eigen.value.Mat1, eigen.value.Mat2 )

   ## for \eta
   Mat1 <- G.Pxcom.G
   Mat2 <- bar.z %*% t(bar.z)
   eigen.value.Mat1 <- eigen.value.S.tau.part1
   eigen.value.Mat2 <- eigen( Mat2, symmetric=TRUE )$values
   eigen.value.eta <- kronecker( eigen.value.Mat1, eigen.value.Mat2 )

   ###### some useful statistics ######

   ## mean and variance for \xi, df, mean and sigma for approx. chi2
   mix.chi2.xi <- Para_Match_Kur(eigen.value.xi)

   ## mean and variance for \eta, df, mean and sigma for approx. chi2
   mix.chi2.eta <- Para_Match_Kur(eigen.value.eta)


   ## variance for zeta
   Mat1 <- (W^{1/2}) %*% t(G) %*% P.x.com %*% GGt %*% P.x.com %*% G %*% (W^{1/2})
   Mat2 <- t(Z) %*% M %*% ( Z %*% t(Z) ) %*% ( diag(1,K) - M ) %*% Z
   var.zeta <- 4 * sum( diag( Mat1 ) ) * sum( diag( Mat2 ) )

   ## mean and variance for kappa
   mu.kappa <- mix.chi2.xi$mu.Q
   var.kappa <- (mix.chi2.xi$sigma.Q)^2 + var.zeta


   ## set grid of rho
   p.rho <- rep( NA, length(rho) )
   lambda.rho <- list(NA)
   S.tau.rho <- rep(NA,length(rho))
   

   for ( v in 1:length(rho) )
   { 
      rho.v <- rho[v]
      R.rho.v <- ( 1-rho.v ) * diag( 1, K ) + rho.v * rep( 1,K ) %*% t( rep( 1,K ) )

      ## calculate test statistic
      middle.v <- kronecker( GGt, inv.Sigma.hat %*% R.rho.v %*% inv.Sigma.hat )
      S.tau.v <- as.numeric( t( resid ) %*% middle.v %*% resid )
      S.tau.rho[v] <- S.tau.v

      ## calculate p.rho.v 
      Mat2 <- Z %*% R.rho.v %*% Z
      eigen.value.S.tau.part2 <- eigen( Mat2, symmetric=TRUE )$values
      eigen.value.S.tau.v <- kronecker( eigen.value.S.tau.part1, eigen.value.S.tau.part2 )

      lambda.rho[[v]] <- eigen.value.S.tau.v 

      ## use davies method to compute p-value 
      pvalue.davies <- davies( S.tau.rho[v] , lambda.rho[[v]] )$Qq      

      ## use modified liu method to compute p-value
      mix.S.tau.v <- Para_Match_Kur(lambda.rho[[v]])
      mu.S.tau.v <- mix.S.tau.v$mu.Q
      sigma.S.tau.v <- mix.S.tau.v$sigma.Q
      mu.S.tau.v.approx <- mix.S.tau.v$mu.X
      sigma.S.tau.v.approx <- mix.S.tau.v$sigma.X
      df.S.tau.v.approx <- mix.S.tau.v$df.X

      S.tau.v.norm <- (S.tau.v - mu.S.tau.v) / sigma.S.tau.v * sigma.S.tau.v.approx +  mu.S.tau.v.approx 

      pvalue.liu <- pchisq( S.tau.v.norm, df = df.S.tau.v.approx, lower.tail = FALSE )

      ## if pvalue.davies is between 0 and 1 than use it, otherwise use pvalue.liu
      if( pvalue.davies>0 & pvalue.davies <1 ) { p.rho[v]<-pvalue.davies } else { p.rho[v]<-pvalue.liu }

   }

   ###### new test statistic T ######
   T <- min(p.rho)
   T.id <- which(p.rho==T)
   if (length(T.id>1)) T.id <- T.id[1]

   ###### calculate q_min(rho), tau(rho) for each rho ######
   q.min.rho <- rep( NA, length(rho) )
   tau.rho <- rep( NA, length(rho) )

   bar.z.2 <- (t( bar.z ) %*% bar.z)^2
   bar.z.Z <- sum( ( t( bar.z ) %*% Z )^2 )

   for ( v in 1:length(rho) )
   {
     lambda.v <- lambda.rho[[v]]

     mix.lambda.v <- Para_Match_Kur(lambda.v)
       
     mu.lambda.v <- mix.lambda.v$mu.Q
     sigma.lambda.v <- mix.lambda.v$sigma.Q
     df.lambda.v.approx <- mix.lambda.v$df.X
     mu.lambda.v.approx <- mix.lambda.v$mu.X
     sigma.lambda.v.approx <- mix.lambda.v$sigma.X

     q.min.rho.temp <- qchisq( 1-T, df = df.lambda.v.approx )

     q.min.rho[v] <- ( q.min.rho.temp - mu.lambda.v.approx ) / sigma.lambda.v.approx * sigma.lambda.v + mu.lambda.v
     tau.rho[v] <- ( 1-rho[v] ) * bar.z.Z / bar.z.2 + (K^2) * rho[v]
   }

   ###### calculate p-value for T ###### :: eigen.value.eta
   ## Jan 2, 2015: revise the p.T <- Optimal_PValue(...) part to use new version Optimal_PValue()
   #   p.T <- Optimal_PValue(rho, q.min.rho, tau.rho, mu.kappa, var.kappa,mix.chi2.xi, mix.chi2.eta)
   #out <- list( rho=rho, S.tau.rho=S.tau.rho, p.rho=p.rho, T=T, T.id=T.id, p.T=p.T, iter=fit.null$numIter,
   #             tau.rho=tau.rho, q.rho=q.min.rho, Z=Z, M=M, barZ=bar.z, P.x.com=P.x.com, GGt=GGt,
   #             mu.kappa=mu.kappa, var.kappa=var.kappa,mix.chi2.xi=mix.chi2.xi, mix.chi2.eta=mix.chi2.eta, 
   #             eigen.value.eta = eigen.value.eta)
   p.T <- Optimal_PValue(rho, q.min.rho, tau.rho, mu.kappa, var.kappa,mix.chi2.xi, mix.chi2.eta, eigen.value.eta)
   out <- list( S.rho=S.tau.rho, p.rho=p.rho, rho.v=rho[T.id], T=T, p.T=p.T$p )

  # if (fit.null$numIter == -999) { out$p.T <- NA }	

   if (p==1) message("Only one SNP in the SNP set!")

  # if (is.na(out$p.T)) message("Null model does not converge!")

   return(out)
   
}



## end 