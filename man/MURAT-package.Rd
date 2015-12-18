\name{MURAT-package}
\alias{MURAT-package}
\docType{package}
\title{
\packageTitle{MURAT}
}
\description{
\packageDescription{MURAT}
}
\details{

The DESCRIPTION file:
\packageDESCRIPTION{MURAT}
\packageIndices{MURAT}
An overview of how to use the package, including the most important functions. 
}
\author{
\packageAuthor{MURAT}

Maintainer: \packageMaintainer{MURAT}
}
\references{
Sun, J., Oualkacha, K., Forgetta1, V., Zheng, H.F., Richards, J.B., Ciampi, A., Greenwood1, C.M.T., and UK10K Consortium. (2015) A method for analyzing multiple continuous phenotypes in rare variant association studies allowing for flexible correlations in variant effects. Contidionally accepted by European Journal of Human Genetics.
}
\keyword{ package }
\seealso{
MURAT
}
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
