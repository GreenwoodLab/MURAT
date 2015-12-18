\name{MURAT}
\alias{MURAT}
\title{
MUltivariate Rare-variant Association Test
}
\description{
The main function for conducting Multivariate Rare-variant Association Test.
}
\usage{
MURAT(Y,G,X,rho=seq(0,0.9,by=0.1),weight=FALSE,weight.para1=NA,weight.para2=NA)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{Y}{
A numeric matrix of outcome variables with rows for individuals and columns for multiple continuous traits. Missing values are not allowed.
}
  \item{G}{
A numeric genotype matrix with rows for individuals and columns for SNPs. Each SNP should be coded as 0, 1, or 2, representing the number of minor alleles that an individual carries for this SNP.}
  \item{X}{
A numeric matrix of covariates with rows for individuals and columns for covariates. All elements in the first column of X should be integer 1, representing for intercept.
}
  \item{rho}{
A numeric vector in the range of [0,1), representing correlation for the effects of the same variant on different phenotypes. The default value is a sequence from 0 to 0.9 increasing by 0.1.
}
  \item{weight}{
A logic variable indicating whether a weighted test should be used. The default value is "FALSE". If "True", a weight depending on minor allele frequency will be added to the corresponding SNP.
}
  \item{weight.para1}{
A numeric parameter for weight. See "Details".
}
  \item{weight.para2}{
A numeric parameter for weight. See "Details"
}
}
\details{
When "weight=TRUE", a weighted test is used. The weight for each SNP is a beta fuction of the corresponding minor allele frequency (MAF). There are two parameters, weight.para1 and weight.para2, for beta function. For example, when weight.para1=weight.para2=0.5, the corresponding weight is 1/sqrt(MAF*(1-MAF)); when weight.para=1 and weight.para=25, the corrsponding weight is the one suggested by SKAT.
}
\value{
%Or error message or a list with the following items
\item{S.rho }{Score statistics for each rho value.}
\item{p.rho }{p-values for each S.rho.}
\item{rho.v}{The value of rho that gives the smallest p-values of S.rho.}
\item{T}{Overall test staistic for MURAT.}
\item{p.T}{Overall p-value for MURAT (i.e. the p-value for T).}
%% ...
}
\references{
Sun, J., Oualkacha, K., Forgetta1, V., Zheng, H.F., Richards, J.B., Ciampi, A., Greenwood1, C.M.T., and UK10K Consortium. (2015) A method for analyzing multiple continuous phenotypes in rare variant association studies allowing for flexible correlations in variant effects. Contidionally accepted by European Journal of Human Genetics.
}
\author{
\packageAuthor{MURAT}
}
%% \note{
%%  ~~further notes~~
%% }

%% ~Make other sections like Warning with \section{Warning }{....} ~

%\seealso{
%% ~~objects to See Also as \code{\link{help}}, ~~~
%}
\examples{
data(sample)

## three continuous traits for 500 individuals
Y <- sample$Y

## genotype data of 20 SNPs for 500 individuals
G <- sample$G

## three covairates for 500 individuals
X <- sample$X

## MURAT without weight
re <- MURAT(Y,G,X,rho=seq(0,0.9,by=0.1))

## MURAT with weight function beta(1,25)
re.w1 <- MURAT(Y,G,X,rho=seq(0,0.9,by=0.1),weight=TRUE,weight.para1=1,weight.para2=25 )

## MURAT with weight function beta(0.5,0.5)
re.w2 <- MURAT(Y,G,X,rho=seq(0,0.9,by=0.1),weight=TRUE,weight.para1=0.5,weight.para2=0.5 )

}
\keyword{ main function }
