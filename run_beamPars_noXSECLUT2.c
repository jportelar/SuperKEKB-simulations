#include <iostream>
#include <vector>
#include <time.h>
#include <limits>

#include <TMath.h>
#include <TRandom2.h>
#include <TTree.h>
#include <TFile.h>
#include <TBranch.h>
#include <TMatrixD.h>
#include <TF1.h>
#include <TH1D.h>
#include <TCanvas.h>
#include <TAxis.h>
#include <TLeaf.h>
#include <TString.h>
#include <TPad.h>
#include <TStyle.h>
#include "Math/Minimizer.h"
#include "Math/Factory.h"
#include "Math/Functor.h"
#include "Math/WrappedTF1.h"
#include "Math/Integrator.h"
#include "Fit/ParameterSettings.h"

#include "constants.h"

// global data to be seen by cost function
TH1D* hEg;
double _beamGasEMinCutOff = 0.01e9;
double _Egmax = 10e9;
double _Egmin = 0.e9;
const unsigned int _nBins = 600;
const unsigned int _chi2binMin = 2*_nBins/200.;
double _curEei, _curEnergyResol_A,_curEnergyResol_B,_curMiscalE_scale,_curZ;
const unsigned int lutlen = 20000*_nBins/200.;
const unsigned int lutlen2 = 20000*_nBins/200.;
const unsigned int lutlenConvE = 2000*_nBins/200.;
// LUTs for xsec
double lut0[lutlen];//ymin, ymax
double lut21[lutlen];//ymin, ymax
double lut0_0[lutlen2];//ymin, 2*ymax
double lut0_21[lutlen2];//ymin, 2*ymax
double lut21_21[lutlen2];//ymin, 2*ymax
double lutBG[lutlen];//yBGmin,1.
double lutBG_0[lutlen];//yBGmin,1.
double lutBG_21[lutlen];//yBGmin,1.
// LUTs w/ energy convolution
double lutEconv_0[lutlenConvE];//0,Egmax
double lutEconv_21[lutlenConvE];//0,Egmax
double lutEconv_0_0[lutlenConvE];//0,Egmax
double lutEconv_0_21[lutlenConvE];//0,Egmax
double lutEconv_21_21[lutlenConvE];//0,Egmax
double lutEconv_BG[lutlenConvE];//0,Egmax
double lutEconv_BG_0[lutlenConvE];//0,Egmax
double lutEconv_BG_21[lutlenConvE];//0,Egmax
// LUTs w/ bins
double lutbins_0[_nBins];//0,Egmax
double lutbins_21[_nBins];//0,Egmax
double lutbins_BG[_nBins];//0,Egmax
double lutbins_0_0[_nBins];//0,Egmax
double lutbins_0_21[_nBins];//0,Egmax
double lutbins_21_21[_nBins];//0,Egmax
double lutbins_BG_0[_nBins];//0,Egmax
double lutbins_BG_21[_nBins];//0,Egmax
// LUT beam Gas
TH1D* hEgBeamGasLUT = new TH1D("hEgBeamGasLUT","",_nBins,_Egmin,_Egmax);
TH1D* hEgBeamGasLUT_0 = new TH1D("hEgBeamGasLUT_0","",_nBins,_Egmin,_Egmax);
TH1D* hEgBeamGasLUT_21 = new TH1D("hEgBeamGasLUT_21","",_nBins,_Egmin,_Egmax);

double integAbsTol = 1E-3;
double integRelTol = 1E-3;

double lumi(double siX, double siY, double siZ, double Ni, double sLX, double sLY, double sLZ,double nL,double theta) {

return nL*Ni/(2*TMath::Pi()*TMath::Sqrt(sLY*sLY+siY*siY)*TMath::Sqrt((sLX*sLX+siX*siX)+pow(TMath::Tan(theta/2),2)*(sLZ*sLZ+siZ*siZ)));

}

double y(double omega, double beta, double theta, double Eei) {
    return omega/Eei*(1+beta)/(1-beta*TMath::Cos(theta)+omega*(1+TMath::Cos(theta))/Eei);
}

double inline r_fun(double y, double x) {
    return y/(x*(1-y));
}

double inline xsec0(double x,double y) {
    return 1/x*(1-y+1/(1-y)-4*r_fun(y,x)*(1-r_fun(y,x)));
}

double xsec1(double x,double y) {
    return 1/x*4*r_fun(y,x)*(1-r_fun(y,x));
}

double inline xsec21(double x,double y) {
    return 2*r_fun(y,x)*(2-y)*(1-2*r_fun(y,x));
}

double xsec22(double x,double y) {
    return 1/x*2*r_fun(y,x)*sqrt((1+x)*y*(x/(1+x)-y));
}

double xsec(double x,double y,double phi,double Pz,double Pt,double phiElecPol,double PLasLin,double PLasCirc,double phiLasPol) {
    double result = xsec0(x,y)-xsec1(x,y)*PLasLin*TMath::Cos(2*(phiLasPol-phi));
    result += (xsec21(x,y)*Pz/2-xsec22(x,y)*Pt*TMath::Cos(phi-phiElecPol))*PLasCirc;
    return result*re*re;
}

double xsecTot(double x,double Pz,double PLasCirc) {
    //double xsec0tot = ((x*(16 + x*(2 + x)*(16 + x)))/(2*TMath::Power(1 + x,2) + (-8 + (-4 + x)*x)*TMath::Log(1 + x)))/TMath::Power(x,3);
    double xsec0tot = 1/x*((1-4/x-8/(x*x))*TMath::Log(1 + x)+1/2.+8/x-1/(2*TMath::Power(1+x,2)));
    double xsec21tot = 2*((1 + 2/x)*TMath::Log(1 + x) - 5/2. + 1/(1 + x) - 1/(2*TMath::Power(1+x,2)))/x;
    return 2*TMath::Pi()*(xsec0tot + xsec21tot*Pz/2*PLasCirc)*re*re;
}

double inline xsecTotNorm(double x,double Pz,double PLasCirc) {
    //double xsec0tot = ((x*(16 + x*(2 + x)*(16 + x)))/(2*TMath::Power(1 + x,2) + (-8 + (-4 + x)*x)*TMath::Log(1 + x)))/TMath::Power(x,3);
    double xsec0tot = 1/x*((1-4/x-8/(x*x))*TMath::Log(1 + x)+1/2.+8/x-1/(2*TMath::Power(1+x,2)));
    double xsec21tot = 2*((1 + 2/x)*TMath::Log(1 + x) - 5/2. + 1/(1 + x) - 1/(2*TMath::Power(1+x,2)))/x;
    return xsec0tot + xsec21tot*Pz/2*PLasCirc;
}

double inline xsecBeamGas(double y,double Z) {
    return 4/y*(((1-y)*(1-y)+1-2/3.*(1-y))*(Z*Z*TMath::Log(184.15*TMath::Power(Z,-1/3.))+Z*TMath::Log(1194.*TMath::Power(Z,-2/3.)))+(1-y)*(Z*Z+Z)/9.);
}

double inline xsecBGTot(double Z,double Eei) {
   // return -2/27.*Z*((1-_beamGasEMinCutOff/Eei)*(8 - 3*(_beamGasEMinCutOff/Eei+1.))-8*TMath::Log(Eei/_beamGasEMinCutOff))*(1 + Z + 9*Z*TMath::Log(184.15*TMath::Power(Z,-1/3.)) + 9*TMath::Log(1194.*TMath::Power(Z,-2/3.)));
    return 2/9.*Z*(-2*TMath::Log(_beamGasEMinCutOff/Eei)*(1+Z+12*TMath::Log(1194.*TMath::Power(Z,-2/3.))) + (-1+_beamGasEMinCutOff/Eei)*(2*(1+Z)+(15-9*_beamGasEMinCutOff/Eei)*TMath::Log(1194.*TMath::Power(Z,-2/3.))) - 3*Z*(5-8*_beamGasEMinCutOff/Eei+3*TMath::Power(_beamGasEMinCutOff/Eei,2) + 8*TMath::Log(_beamGasEMinCutOff/Eei))*TMath::Log(184.15*TMath::Power(Z,-1/3.)));
}

double nBGtot(double L, double Pressure, double T, double Z,double Eei) {
    return re*re*alpha*xsecBGTot(Z,Eei)*L*Pressure/(kB*T);
}

double nSR(double y,double Eei,double Bmag,double Lmag) {
    double gamma = Eei/me;
    double rho = Eei/1e9/(0.3*Bmag);
    double EcutoffSR = 3/2.*TMath::Power(gamma,3)*hbarc/rho;
    double ySR = y*Eei/EcutoffSR;
    double nSR = Eei/EcutoffSR*Lmag/(2*TMath::Pi()*rho)*TMath::Sqrt(3*TMath::Pi()/2.)*alpha*gamma*TMath::Exp(-ySR)/TMath::Sqrt(ySR);
    return nSR;
}

double nSRtot(double Eei,double Bmag,double Lmag) {
    double gamma = Eei/me;
    double rho = Eei/(0.3*Bmag);
    double EcutoffSR = 3/2.*TMath::Power(gamma,3)*hbarc/rho;
    return 3*alpha/(4.*TMath::Sqrt(TMath::Pi()))*TMath::Sqrt(hbarc)*TMath::Power(gamma,2.5)/TMath::Power(rho,1.5)*Lmag/TMath::Sqrt(EcutoffSR);
}

double inline resolution(double Eg, double energyResol_A,double energyResol_B) {
    return Eg*TMath::Sqrt(energyResol_A/100.*energyResol_A/100./(Eg/1e9)+energyResol_B/100.*energyResol_B/100.);
}

double chi2pdf(Double_t *x,Double_t *par)
{
// Chisquare density distribution for nrFree degrees of freedom
Double_t chi2 = x[0];

if (chi2 > 0) {
Double_t lambda = par[0]/2.;
Double_t norm = TMath::Gamma(lambda)*TMath::Power(2.,lambda);
return par[1]*TMath::Power(chi2,lambda-1)*TMath::Exp(-0.5*chi2)/norm;
} else
return 0.0;
}

double convol2phLUTBG0(double *x, double *par) {
    double yc1 = x[0];
    double ytot = par[0];
    double x0 = par[1];
    double ymax = par[2];
    double ymin = par[3];
    double Z=par[4];
    
    double yc2 = ytot-yc1;
    if (( (yc2>_beamGasEMinCutOff/_curEei && yc1>ymin) || (yc1>0 && yc2>_beamGasEMinCutOff/_curEei) ) && yc1<ymax && yc2<1.) {
        return  xsec0(x0,yc1)*xsecBeamGas(yc2,Z);
    }
    else
        return 0;
}

double convol2phLUTBG21(double *x, double *par) {
    double yc1 = x[0];
    double ytot = par[0];
    double x0 = par[1];
    double ymax = par[2];
    double ymin = par[3];
    double Z=par[4];
    
    double yc2 = ytot-yc1;
    if ( ( (yc2>_beamGasEMinCutOff/_curEei && yc1>ymin) || (yc1>0 && yc2>_beamGasEMinCutOff/_curEei) ) && yc1<ymax && yc2<1.) {
        return  xsec21(x0,yc1)/2.*xsecBeamGas(yc2,Z);
    }
    else
        return 0;
}


double convol2phLUT00(double *x, double *par) {
    double yc1 = x[0];
    double ytot = par[0];
    double x0 = par[1];
    double ymax = par[2];
    double ymin = par[3];
    
    double yc2 = ytot-yc1;
    if (((yc2>0 && yc1>ymin) || (yc1>0 && yc2>ymin) )&& yc2<ymax && yc1<ymax) {
        return  xsec0(x0,yc1)*xsec0(x0,yc2);
    }
    else
        return 0;
}

double convol2phLUT021(double *x, double *par) {
    double yc1 = x[0];
    double ytot = par[0];
    double x0 = par[1];
    double ymax = par[2];
    double ymin = par[3];
    
    double yc2 = ytot-yc1;
    if (((yc2>0 && yc1>ymin) || (yc1>0 && yc2>ymin) )&& yc2<ymax && yc1<ymax) {
        return  xsec0(x0,yc1)*xsec21(x0,yc2)/2.+xsec21(x0,yc1)/2.*xsec0(x0,yc2);
    }
    else
        return 0;
}

double convol2phLUT2121(double *x, double *par) {
    double yc1 = x[0];
    double ytot = par[0];
    double x0 = par[1];
    double ymax = par[2];
    double ymin = par[3];
    
    double yc2 = ytot-yc1;
    if (((yc2>0 && yc1>ymin) || (yc1>0 && yc2>ymin) )&& yc2<ymax && yc1<ymax) {
        return  xsec21(x0,yc1)*xsec21(x0,yc2)/4.;
    }
    else
        return 0;
}

void fillLUT(double x0, double ymin, double ymax, double Z) {
    //cout << "FILL LUT" << endl
    
    double halfBinSize = (ymax-ymin)/((double) 2*lutlen);
    for (unsigned int k=0;k<lutlen;k++) {
        double yc = ymin+(1+k*2)*halfBinSize;//(ymax-ymin)/((double) lutlen-1.);
        lut0[k] = xsec0(x0,yc);
        lut21[k] = xsec21(x0,yc)/2.; //*pz*plascirc
    }
    
    halfBinSize = (2*ymax-ymin)/((double) 2*lutlen2);
    for (unsigned int kt=0;kt<lutlen2;kt++) {
        double ytot = ymin+(1+kt*2)*halfBinSize;
        
        const double parConvol[4]={ytot,x0,ymax,ymin};
        TF1 f("convol2phLUT00",convol2phLUT00,0,ymax,4);
        f.SetParameters(parConvol);
        ROOT::Math::WrappedTF1 wf(f);
        ROOT::Math::Integrator ig(wf, ROOT::Math::IntegrationOneDim::kADAPTIVE);
        ig.SetAbsTolerance(integAbsTol);
        ig.SetRelTolerance(integRelTol);
        lut0_0[kt] = ig.Integral(0,ymax);
        
        TF1 f2("convol2phLUT021",convol2phLUT021,0,ymax,4);
        f2.SetParameters(parConvol);
        ROOT::Math::WrappedTF1 wf2(f2);
        ROOT::Math::Integrator ig2(wf2, ROOT::Math::IntegrationOneDim::kADAPTIVE);
        ig2.SetAbsTolerance(integAbsTol);
        ig2.SetRelTolerance(integRelTol);
        lut0_21[kt] = ig2.Integral(0,ymax);
        
        TF1 f3("convol2phLUT2121",convol2phLUT2121,0,ymax,4);
        f3.SetParameters(parConvol);
        ROOT::Math::WrappedTF1 wf3(f3);
        ROOT::Math::Integrator ig3(wf3, ROOT::Math::IntegrationOneDim::kADAPTIVE);
        ig3.SetAbsTolerance(integAbsTol);
        ig3.SetRelTolerance(integRelTol);
        lut21_21[kt] = ig3.Integral(0,ymax);
    }
    
    //BG
    double yminBG=_beamGasEMinCutOff/_curEei;
    double ymaxBG=1.;
    halfBinSize = (ymaxBG-yminBG)/((double) 2*lutlen);
    for (unsigned int k=0;k<lutlen;k++) {
        double y = yminBG+(1+k*2)*halfBinSize;
        lutBG[k] = xsecBeamGas(y,Z);
        
        const double parConvol[5]={y,x0,ymax,ymin,Z};
        TF1 f("convol2phLUTBG0",convol2phLUTBG0,0,ymax,5);
        f.SetParameters(parConvol);
        ROOT::Math::WrappedTF1 wf(f);
        ROOT::Math::Integrator ig(wf, ROOT::Math::IntegrationOneDim::kADAPTIVE);
        ig.SetAbsTolerance(integAbsTol);
        ig.SetRelTolerance(integRelTol);
        lutBG_0[k] = ig.Integral(0,1.);
        
        TF1 f2("convol2phLUTBG21",convol2phLUTBG0,0,ymax,5);
        f2.SetParameters(parConvol);
        ROOT::Math::WrappedTF1 wf2(f2);
        ROOT::Math::Integrator ig2(wf2, ROOT::Math::IntegrationOneDim::kADAPTIVE);
        ig2.SetAbsTolerance(integAbsTol);
        ig2.SetRelTolerance(integRelTol);
        lutBG_21[k] = ig2.Integral(0,1.);
    }
    
    /*//sanity check
    double sum1=0;
    for (unsigned int k=0;k<lutlen;k++) {
        sum1 += lut0[k];
    }
    sum1*=(ymax-ymin)/((double) lutlen-1)/xsecTotNorm(x0,0,0.);
    double sum2=0;
    for (unsigned int k=0;k<lutlen2;k++) {
        sum2 += lut0_0[k];
    }
    sum2*=(2*ymax-ymin)/((double) lutlen2-1)/(xsecTotNorm(x0,0,0.)*xsecTotNorm(x0,0,0.));
    
    cout << sum1 <<  " " << sum2 << endl;*/
}

double convolE(double *x, double *par) {
    
    double Egc = x[0];
    double Eg = par[0]; //measured
    double ymax = par[1];
    double ymin = par[2];
    double x0 = par[3];
    double Z = par[4];
    int choice = (int) par[5];
    //10 = 1ph, unpol lut0
    //11 = 1ph, circ pol term lut21
    //12 = 1ph, BG
    //20 = 2ph, unpol lut0_0
    //21 = 2ph, circ pol term lut0_21
    //22 = 2ph, square circ pol term lut21_21
    //23 = 2ph, unpol BG x lut_0
    //24 = 2ph, BG x circ pol term lutBG_21

    double yc=Egc/_curEei;
    double sigEgc = resolution(Egc,_curEnergyResol_A,_curEnergyResol_B);
    //cout << _curEnergyResol_A << " " << _curEnergyResol_B << " " <<Egc << " " << sigEgc << endl;
    double xsec = 0;
    
    double yminBG=_beamGasEMinCutOff/_curEei;
    double ymaxBG=1.;
    
    switch ( choice )
    {
        case 10:
            if (yc<ymax && yc>ymin) {
                /*double index = (yc-ymin)/(ymax-ymin)*((double) lutlen-1.);
                int id = index;
                double residual = index-id;
                xsec = (1.-residual)*lut0[id]+residual*lut0[id+1];*/
                xsec=xsec0(x0,yc);
            }
            break;
        case 11:
            if (yc<ymax && yc>ymin) {
                /*double index = (yc-ymin)/(ymax-ymin)*((double) lutlen-1.);
                int id = index;
                double residual = index-id;
                xsec = (1.-residual)*lut21[id]+residual*lut21[id+1];*/
                xsec=xsec21(x0,yc)/2.;
            }
            break;
        case 12:
            if (yc<ymaxBG && yc>yminBG) {
                xsec=xsecBeamGas(yc,Z);
                /*if (yc<0.02)
                    cout << std::setprecision(15) << Egc << " " << " " << yc << " " << xsec << endl;*/
            }
            break;
        case 20:
            if (yc<2*ymax && yc>ymin) {
                double index = (yc-ymin)/((2*ymax-ymin))*((double) lutlen2);
                int id = index;
                double residual = index-id;
                if ((id+1)<lutlen2)
                    xsec = (1.-residual)*lut0_0[id]+residual*lut0_0[id+1];
                else
                    xsec = lut0_0[id];
            }
            break;
        case 21:
            if (yc<2*ymax && yc>ymin) {
                double index = (yc-ymin)/((2*ymax-ymin))*((double) lutlen2);
                int id = index;
                double residual = index-id;
                if ((id+1)<lutlen2)
                    xsec = (1.-residual)*lut0_21[id]+residual*lut0_21[id+1];
                else
                    xsec = lut0_21[id];
            }
            break;
        case 22:
            if (yc<2*ymax && yc>ymin) {
                double index = (yc-ymin)/((2*ymax-ymin))*((double) lutlen2);
                int id = index;
                double residual = index-id;
                if ((id+1)<lutlen2)
                    xsec = (1.-residual)*lut21_21[id]+residual*lut21_21[id+1];
                else
                    xsec = lut21_21[id];
                
            }
            break;
        case 23:
            if (yc<ymaxBG && yc>yminBG) {
                double index = (yc-yminBG)/(ymaxBG-yminBG)*((double) lutlen);
                int id = index;
                double residual = index-id;
                if ((id+1)<lutlen)
                    xsec = (1.-residual)*lutBG_0[id]+residual*lutBG_0[id+1];
                else
                    xsec = lutBG_0[id];
                
            }
            break;
        case 24:
            if (yc<ymaxBG && yc>yminBG) {
                double index = (yc-yminBG)/(ymaxBG-yminBG)*((double) lutlen);
                int id = index;
                double residual = index-id;
                if ((id+1)<lutlen)
                    xsec = (1.-residual)*lutBG_21[id]+residual*lutBG_21[id+1];
                else
                    xsec = lutBG_21[id];
            }
            break;
       default:
            cout << "ERROR: unknown case for swtich statement in convolE" << endl;
    }
    
    return xsec*TMath::Gaus(Eg,Egc,sigEgc,kTRUE);
}

void fillLUTconvolE(double x0, double ymin, double ymax,double Z) {
    
    const double parConvol[6]={0.,ymax,ymin,x0,Z,0};
    TF1 f("convolE",convolE,0,_Egmax,6);
    f.SetParameters(parConvol);
    ROOT::Math::WrappedTF1 wf(f);
    ROOT::Math::Integrator ig(wf, ROOT::Math::IntegrationOneDim::kADAPTIVE);
    ig.SetAbsTolerance(integAbsTol);
    ig.SetRelTolerance(integRelTol);
    
    double halfBinSize = (_Egmax-_Egmin)/((double) 2*lutlenConvE);
    for (unsigned int kt=0;kt<lutlenConvE;kt++) {
        double Eg = _Egmin+(1+2*kt)*halfBinSize;
        double sigE = resolution(Eg,_curEnergyResol_A,_curEnergyResol_B);
        double minEgc = TMath::Max(Eg-5*sigE,_Egmin);
        double maxEgc = TMath::Min(Eg+5*sigE,_Egmax);
        double minc = TMath::Max(minEgc,ymin*_curEei);
        double maxc = TMath::Min(maxEgc,ymax*_curEei);
        double maxc2 = TMath::Min(maxEgc,2*ymax*_curEei);
        double minBG = TMath::Max(minEgc,_beamGasEMinCutOff);
        double maxBG = TMath::Min(maxEgc,_curEei);
        
        f.SetParameter(0,Eg);
        
        if (minc<maxc) {
            f.SetParameter(5,10);
            lutEconv_0[kt] = ig.Integral(minc,maxc);
            
            f.SetParameter(5,11);
            lutEconv_21[kt] = ig.Integral(minc,maxc);
        }
        else {
            lutEconv_0[kt] = 0;
            lutEconv_21[kt] = 0;
        }
        
        if (minc<maxc2) {
            f.SetParameter(5,20);
            lutEconv_0_0[kt] = ig.Integral(minc,maxc2);
            
            f.SetParameter(5,21);
            lutEconv_0_21[kt] = ig.Integral(minc,maxc2);
            
            f.SetParameter(5,22);
            lutEconv_21_21[kt] = ig.Integral(minc,maxc2);
        }
        else {
            lutEconv_0_0[kt] = 0;
            lutEconv_0_21[kt] = 0;
            lutEconv_21_21[kt] = 0;
        }
        
       /* if (minBG<maxBG) {
            f.SetParameter(5,12);
            lutEconv_BG[kt] = ig.Integral(minBG,maxBG);
            
            f.SetParameter(5,23);
            lutEconv_BG_0[kt] = ig.Integral(minBG,maxBG);
            
            f.SetParameter(5,24);
            lutEconv_BG_21[kt] = ig.Integral(minBG,maxBG);
            
            if (kt<60 ) {
                cout << Eg << " " << minBG << " " << maxBG << " "  << lutEconv_BG[kt] << " " << xsecBeamGas(Eg/_curEei,Z) << endl;
                
            }
        }
        else {
            lutEconv_BG[kt] = 0;
            lutEconv_BG_0[kt] = 0;
            lutEconv_BG_21[kt] = 0;
        }*/
    }
}

double computeBins(double *x, double *par) {
    
    double Eg = x[0];  //measured
    int choice = (int) par[0];
    //10 = 1ph, unpol lut0
    //11 = 1ph, circ pol term lut21
    //12 = 1ph, BG
    //20 = 2ph, unpol lut0_0
    //21 = 2ph, circ pol term lut0_21
    //22 = 2ph, square circ pol term lut21_21
    //23 = 2ph, unpol BG x lut_0
    //24 = 2ph, BG x circ pol term lutBG_21
    
    double  index  = (Eg-_Egmin)/(_Egmax-_Egmin)*((double) lutlenConvE);
    int id = index;
    double residual = index-id;

    double value = 0;
    if ((id+1)<lutlenConvE) {
        switch ( choice )
        {
            case 10:
                value = (1.-residual)*lutEconv_0[id]+residual*lutEconv_0[id+1];
                break;
            case 11:
                value = (1.-residual)*lutEconv_21[id]+residual*lutEconv_21[id+1];
                break;
            case 12:
                value = (1.-residual)*lutEconv_BG[id]+residual*lutEconv_BG[id+1];
                break;
            case 20:
                value = (1.-residual)*lutEconv_0_0[id]+residual*lutEconv_0_0[id+1];
                break;
            case 21:
                value = (1.-residual)*lutEconv_0_21[id]+residual*lutEconv_0_21[id+1];
                break;
            case 22:
                value = (1.-residual)*lutEconv_21_21[id]+residual*lutEconv_21_21[id+1];
                break;
            case 23:
                value = (1.-residual)*lutEconv_BG_0[id]+residual*lutEconv_BG_0[id+1];
                break;
            case 24:
                value = (1.-residual)*lutEconv_BG_21[id]+residual*lutEconv_BG_21[id+1];
                break;
           default:
                cout << "ERROR: unknown case for swtich statement in computeBins" << endl;
        }
    }
    else if (id<lutlenConvE) {
        switch ( choice )
        {
            case 10:
                value = lutEconv_0[id];
                break;
            case 11:
                value = lutEconv_21[id];
                break;
            case 12:
                value = lutEconv_BG[id];
                break;
            case 20:
                value = lutEconv_0_0[id];
                break;
            case 21:
                value = lutEconv_0_21[id];
                break;
            case 22:
                value = lutEconv_21_21[id];
                break;
            case 23:
                value = lutEconv_BG_0[id];
                break;
            case 24:
                value = lutEconv_BG_21[id];
                break;
           default:
                cout << "ERROR: unknown case for swtich statement in computeBins" << endl;
        }
    }
   /* if (Eg<hEg->GetBinCenter(5+1))
        cout << Eg << " " << index << " " << (_Egmax-_Egmin)/((double) lutlenConvE) << " " << value << " " << xsecBeamGas(Eg/_curEei,7.) << endl;*/
    
    return value;
}

void fillLUTbinsInterp() {
    
    ROOT::Math::Interpolator ig_0(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_21(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_BG(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_0_0(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_0_21(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_21_21(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_BG_0(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    ROOT::Math::Interpolator ig_BG_21(/*unsigned int ndata=*/0, /*Interpolation::Type type=*/ROOT::Math::Interpolation::kCSPLINE);
    double lutEconv_x[lutlenConvE];
    double halfBinSize=(_Egmax-_Egmin)/((double) 2*lutlenConvE);
    for (unsigned int kt=0;kt<lutlenConvE;kt++) {
        lutEconv_x[kt] = _Egmin+(1+2*kt)*halfBinSize;
    }
    ig_0.SetData(lutlenConvE,lutEconv_x,lutEconv_0);
    ig_21.SetData(lutlenConvE,lutEconv_x,lutEconv_21);
    ig_BG.SetData(lutlenConvE,lutEconv_x,lutEconv_BG);
    ig_0_0.SetData(lutlenConvE,lutEconv_x,lutEconv_0_0);
    ig_0_21.SetData(lutlenConvE,lutEconv_x,lutEconv_0_21);
    ig_21_21.SetData(lutlenConvE,lutEconv_x,lutEconv_21_21);
    ig_BG_0.SetData(lutlenConvE,lutEconv_x,lutEconv_BG_0);
    ig_BG_21.SetData(lutlenConvE,lutEconv_x,lutEconv_BG_21);
    
    for (unsigned int kt=0;kt<_nBins;kt++) {
        double Eg = (hEg->GetBinCenter(kt+1));
        double width =(hEg->GetBinWidth(kt+1));
        double min = TMath::Max(_Egmin,Eg-width/2)/_curMiscalE_scale;
        double max = TMath::Min(_Egmax,Eg+width/2)/_curMiscalE_scale;
       
        if (max>min) {
            lutbins_0[kt] = ig_0.Integ(min,max);
            
            lutbins_21[kt] = ig_21.Integ(min,max);
            
            lutbins_0_0[kt] = ig_0_0.Integ(min,max);
            
            lutbins_0_21[kt] = ig_0_21.Integ(min,max);
            
            lutbins_21_21[kt] = ig_21_21.Integ(min,max);
            
           // lutbins_BG_0[kt] = ig_BG_0.Integ(min,max);
            
          //  lutbins_BG_21[kt] = ig_BG_21.Integ(min,max);
        }
        else {
            lutbins_0[kt] = 0;
            lutbins_21[kt] = 0;
            lutbins_BG[kt] = 0;
            lutbins_0_0[kt] = 0;
            lutbins_0_21[kt] = 0;
            lutbins_BG_0[kt] = 0;
            lutbins_BG_21[kt] = 0;
            lutbins_21_21[kt] = 0;
        }
        
       /* min = TMath::Max(_beamGasEMinCutOff,Eg-width/2)/_curMiscalE_scale;
        if (max>min) {
            lutbins_BG[kt] = ig_BG.Integ(min,max);
        }
        
        if (Eg<hEg->GetBinCenter(5+1))
            cout << Eg << " " << lutbins_BG[kt] << " " << (Eg>_beamGasEMinCutOff)*xsecBeamGas(Eg/_curEei,7.)*width << endl;*/
    }
}

void fillLUTbinsBeamGas() {
    
    cout << "hello" << endl;

    double Afact=6.1; //has been empirically obtained with mathematica
    int nMax = 1e8;
    TRandom2 rand;
    rand.SetSeed(1500);
    for (int kph=0;kph<nMax;kph++) {
        double Xrnd = rand.Rndm();
        double etaMin=TMath::Log(_beamGasEMinCutOff/_curEei);
        double eta = Afact - sqrt(Afact*Afact + (1-Xrnd)*(etaMin*etaMin- 2*Afact*etaMin));
        double xsec_rnd = rand.Rndm()*((Afact-eta));
        double y = TMath::Exp(eta);
        double xsec_calc = TMath::Log(xsecBeamGas(y,_curZ))-TMath::Log(4/*alpha*re*re*/);
        if (xsec_calc>((Afact-eta)))
            cout << "ERROR " << eta << " " << ((Afact-eta)) << " " << xsec_calc << endl;
        
        if (xsec_rnd<xsec_calc) {
            double Eg = y*_curEei;
            double resolE = resolution(Eg,_curEnergyResol_A,_curEnergyResol_B);
            double Eg_meas = _curMiscalE_scale*(Eg+rand.Gaus(0,resolE));
            hEgBeamGasLUT->Fill(Eg_meas,1/((double) nMax));
        }
        else {
            kph--;
        }
        //if (kph%10000==0)
        //    cout << kph << endl;
    }
    
    double cumbins_0[_nBins];
    double cumbins_21[_nBins];
    cumbins_0[0]=0;
    cumbins_21[0]=0;
    for (unsigned int k=1;k<_nBins;k++) {
        cumbins_0[k] = cumbins_0[k-1]+lutbins_0[k];
        cumbins_21[k] = cumbins_21[k-1]+lutbins_21[k];
    }
    double scale_0 =cumbins_0[_nBins-1];
    double scale_21 =cumbins_21[_nBins-1];
    for (unsigned int k=1;k<_nBins;k++) {
        cumbins_0[k] /= scale_0;
        cumbins_21[k] /= scale_21;
    }
    nMax = 1e6;
    for (int kph=0;kph<nMax;kph++) {
        //double Eg = hEgBeamGasLUT->GetRandom(&rand);
        double Xrnd = rand.Rndm();
        double etaMin=TMath::Log(_beamGasEMinCutOff/_curEei);
        double eta = Afact - sqrt(Afact*Afact + (1-Xrnd)*(etaMin*etaMin- 2*Afact*etaMin));
        double xsec_rnd = rand.Rndm()*((Afact-eta));
        double y = TMath::Exp(eta);
        double xsec_calc = TMath::Log(xsecBeamGas(y,_curZ))-TMath::Log(4/*alpha*re*re*/);
        if (xsec_calc>((Afact-eta)))
            cout << "ERROR " << eta << " " << ((Afact-eta)) << " " << xsec_calc << endl;
        
        if (xsec_rnd<xsec_calc) {
            double Eg = y*_curEei;
        
            double r1 = rand.Rndm();
            int ibin = TMath::BinarySearch(_nBins,cumbins_0,r1);
            double Eg_0 = Eg+hEg->GetBinLowEdge(ibin+1);
            Eg_0 += hEg->GetBinWidth(ibin+1)*(r1-cumbins_0[ibin])/(cumbins_0[ibin+1] - cumbins_0[ibin]);
            
            double resolE = resolution(Eg_0,_curEnergyResol_A,_curEnergyResol_B);
            double Eg_meas = _curMiscalE_scale*(Eg_0+rand.Gaus(0,resolE));
            hEgBeamGasLUT_0->Fill(Eg_meas,1/((double) nMax));
            
            //cout  << Eg_0 << " " << Eg << " " << Eg_meas << endl;
            
            Eg = hEgBeamGasLUT->GetRandom(&rand);
            r1 = rand.Rndm();
            ibin = TMath::BinarySearch(_nBins,cumbins_21,r1);
            double Eg_21 = Eg+hEg->GetBinLowEdge(ibin+1);
            Eg_21 += hEg->GetBinWidth(ibin+1)*(r1-cumbins_21[ibin])/(cumbins_21[ibin+1] - cumbins_21[ibin]);
            
            resolE = resolution(Eg_21,_curEnergyResol_A,_curEnergyResol_B);
            Eg_meas = _curMiscalE_scale*(Eg_21+rand.Gaus(0,resolE));
            hEgBeamGasLUT_21->Fill(Eg_meas,scale_21/scale_0/((double) nMax));
            
        }
        else {
            kph--;
        }
            
            //cout  << Eg_21 << " " << Eg << " " << Eg_meas << endl;
    }
    
    /*double total_0=0;
    double total_21=0;
    for (int kph=0;kph<_nBins;kph++) {
        cout << kph << " " << hEgBeamGasLUT->GetBinCenter(kph+1) << " " << hEgBeamGasLUT->GetBinContent(kph+1) << " " << hEgBeamGasLUT_0->GetBinContent(kph+1) << " " << hEgBeamGasLUT_21->GetBinContent(kph+1)  << endl;
        total_0 +=hEgBeamGasLUT_0->GetBinContent(kph+1);
        total_21 +=hEgBeamGasLUT_21->GetBinContent(kph+1);
    }
    //cout << total_0 << " " << total_21 << endl;
    */
}

void fillLUTbinsInteg() {
    
    const double parBins[1]={0.};
    TF1 f("computeBins",computeBins,_Egmin,_Egmax,1);
    f.SetParameters(parBins);
    ROOT::Math::WrappedTF1 wf(f);
    ROOT::Math::Integrator ig(wf, ROOT::Math::IntegrationOneDim::kADAPTIVE);
    ig.SetAbsTolerance(integAbsTol);
    ig.SetRelTolerance(integRelTol);
    
    for (unsigned int kt=0;kt<_nBins;kt++) {
        double Eg = (hEg->GetBinCenter(kt+1));
        double width =(hEg->GetBinWidth(kt+1));
        double min = TMath::Max(_Egmin,Eg-width/2)/_curMiscalE_scale;
        double max = TMath::Min(_Egmax,Eg+width/2)/_curMiscalE_scale;
       
        if (max>min) {
        f.SetParameter(0,10);
        lutbins_0[kt] = ig.Integral(min,max);
        
        f.SetParameter(0,11);
        lutbins_21[kt] = ig.Integral(min,max);
            
        //f.SetParameter(0,12);
        //lutbins_BG[kt] = ig.Integral(min,max);
        
        f.SetParameter(0,20);
        lutbins_0_0[kt] = ig.Integral(min,max);
        
        f.SetParameter(0,21);
        lutbins_0_21[kt] = ig.Integral(min,max);
        
        f.SetParameter(0,22);
        lutbins_21_21[kt] = ig.Integral(min,max);
        
        /*f.SetParameter(0,23);
        lutbins_BG_0[kt] = ig.Integral(min,max);
        
        f.SetParameter(0,24);
        lutbins_BG_21[kt] = ig.Integral(min,max);*/
        }
        else {
            lutbins_0[kt] =0;
            lutbins_21[kt] =0;
            lutbins_BG[kt] =0;
            lutbins_0_0[kt] =0;
            lutbins_0_21[kt] = 0;
            lutbins_21_21[kt] = 0;
            lutbins_BG_0[kt] = 0;
            lutbins_BG_21[kt] = 0;
        }
        
        //min = TMath::Max(_beamGasEMinCutOff,Eg-width/2)/_curMiscalE_scale;
       /* if (max>min) {
            f.SetParameter(0,12);
            lutbins_BG[kt] = ig.Integral(min,max);
        }
        cout << kt << " " << Eg << " " << lutbins_BG[kt] << " " << xsecBeamGas(Eg/_curEei,7.)*(width) << endl;*/
    }
}

void fillLUTbins() {
    fillLUTbinsInteg();
    fillLUTbinsBeamGas();
}

    
double inline functionEval(int ibin,double f1, double f2,double Pz,double PLasCirc,double norm,double x0,double nExp,double f3, double nBGExp, double Z, double f4) {
    
    //cout <<lutbins_0[ibin] << " " <<lutbins_21[ibin] << endl;
    
    double value = f1*TMath::PoissonI(1,nExp)*(lutbins_0[ibin] + lutbins_21[ibin]*Pz*PLasCirc);
    value += f2*TMath::PoissonI(2,nExp)*(lutbins_0_0[ibin] + (lutbins_0_21[ibin]+lutbins_21_21[ibin]*Pz*PLasCirc)*Pz*PLasCirc)/xsecTotNorm(x0,Pz,PLasCirc);
    value *= norm/(xsecTotNorm(x0,Pz,PLasCirc)*_curEei);
    //double valueBG = f3*TMath::PoissonI(1,nBGExp)*lutbins_BG[ibin];
    //valueBG += f4*TMath::PoissonI(1,nBGExp)*TMath::PoissonI(1,nExp)*(lutbins_BG_0[ibin]+lutbins_BG_21[ibin]*Pz*PLasCirc)/(xsecTotNorm(x0,Pz,PLasCirc));
    //valueBG *= norm/(xsecBGTot(Z,_curEei)*_curEei);
    double valueBG = f3*xsecBGTot(Z,7e9)/xsecBGTot(2.5,7e9)*TMath::PoissonI(1,nBGExp)*hEgBeamGasLUT->GetBinContent(ibin+1);
    //cout << ibin << " " << hEg->GetBinCenter(ibin+1) << " " << valueBG << endl;
    valueBG += /*f4*/f1*f3*xsecBGTot(Z,7e9)/xsecBGTot(2.5,7e9)*TMath::PoissonI(1,nBGExp) *TMath::PoissonI(1,nExp)*(hEgBeamGasLUT_0->GetBinContent(ibin+1)+hEgBeamGasLUT_21->GetBinContent(ibin+1)*Pz*PLasCirc);
    //cout << valueBG << " " << hEgBeamGasLUT_0->GetBinContent(ibin+1) << " " << hEgBeamGasLUT_21->GetBinContent(ibin+1) << " " << f4*TMath::PoissonI(1,nBGExp)*TMath::PoissonI(1,nExp)*norm << endl;
    valueBG *= norm;
    //cout << f3 << " " << TMath::PoissonI(1,nBGExp) << " " << norm << " " <<  valueBG << endl;
    //if(ibin<10)
    //    cout << ibin  << " " << lutbins_BG[ibin] << " " << valueBG << endl;
    return value+valueBG;
    
}



double chi2(const double *xx)
{
    const Double_t scale = xx[0];
    const Double_t Pz = xx[1];
    const Double_t Pt = xx[2];
    const Double_t phiElecPol = xx[3];
    const Double_t PLasLin = xx[4];
    const Double_t PLasCirc = xx[5];
    const Double_t phiLasPol = xx[6];
    const Double_t mEei = xx[7]*1e9;
    const Double_t sEei = xx[8]*1e9;
    const Double_t energyResol_A = xx[9];
    const Double_t energyResol_B = xx[10];
    const Double_t lumi = xx[11];
    const Double_t Nturns = xx[12];
    const Double_t omega = xx[13];
    const Double_t thetaIn = xx[14];
    const Double_t maxAngle = xx[15];
    const Double_t miscalE_scale = xx[16];
    const Double_t scale2 = xx[17];
    const Double_t nExp = xx[18];
    const Double_t Z = xx[19];
    const Double_t scale3 = xx[20];
    const Double_t nBGExp = xx[21];
    const Double_t scale4 = xx[22];
    
    double gamma = mEei/me;
    double beta = TMath::Sqrt(1-1/(gamma*gamma));
    double x0 = 2*gamma*omega/me*(1+beta*TMath::Cos(thetaIn));
    double ymax = x0/(2*gamma*gamma*(1-beta) + x0*(1+TMath::Cos(thetaIn))/(1+beta*TMath::Cos(thetaIn)));
    double ymin = x0/(x0+2*gamma*gamma*(1-beta*TMath::Cos(maxAngle)));
    
    double epsilon = std::numeric_limits<double>::epsilon();
    
    // store lut for current mEei value
    if (abs(mEei-_curEei)>2*epsilon*mEei) {
        _curEei = mEei;
        _curEnergyResol_A = energyResol_A;
        _curEnergyResol_B = energyResol_B;
        _curMiscalE_scale = miscalE_scale;
        _curZ = Z;
        double gamma = _curEei/me;
        double beta = TMath::Sqrt(1-1/(gamma*gamma));
        double x0 = 2*gamma*omega/me*(1+beta*TMath::Cos(thetaIn));
        double ymax = x0/(2*gamma*gamma*(1-beta) + x0*(1+TMath::Cos(thetaIn))/(1+beta*TMath::Cos(thetaIn)));
        double ymin = x0/(x0+2*gamma*gamma*(1-beta*TMath::Cos(maxAngle)));
        fillLUT(x0,ymin,ymax,Z);
        fillLUTconvolE(x0,ymin,ymax,Z);
        fillLUTbins();
    }
    else if (abs(energyResol_A-_curEnergyResol_A)>(2*epsilon*energyResol_A) || abs(energyResol_B-_curEnergyResol_B)>(2*epsilon*energyResol_B)) {
        _curEnergyResol_A = energyResol_A;
        _curEnergyResol_B = energyResol_B;
        _curMiscalE_scale = miscalE_scale;
        _curZ = Z;
        fillLUTconvolE(x0,ymin,ymax,Z);
        fillLUTbins();
    }
    else if (abs(miscalE_scale-_curMiscalE_scale)>(2*epsilon*miscalE_scale)) {
        _curMiscalE_scale = miscalE_scale;
        _curZ = Z;
        //cout <<_curMiscalE_scale << endl;
        fillLUTbins();
    }
    else if (abs(Z-_curZ)>2*epsilon*Z) {
        _curZ = Z;
        fillLUTbinsBeamGas();
    }
    
    // init chi2
    double chi2 = 0;
    for (unsigned int k=0;k<_nBins;k++) {
        //retrieve current data point
        double hval =(hEg->GetBinContent(k+1));
        double herr =(hEg->GetBinError(k+1));
        double func = functionEval(k,scale,scale2,Pz,PLasCirc,Nturns,x0,nExp,scale3,nBGExp,Z,scale4);

        double val=(hval-func)*(hval-func);
        
        if (herr>0)
            val/=herr*herr;
        
        if(k>_chi2binMin)
            chi2+=val;
    }
    
    return chi2;
}

double ML(const double *xx)
{
    const Double_t scale = xx[0];
    const Double_t Pz = xx[1];
    const Double_t Pt = xx[2];
    const Double_t phiElecPol = xx[3];
    const Double_t PLasLin = xx[4];
    const Double_t PLasCirc = xx[5];
    const Double_t phiLasPol = xx[6];
    const Double_t mEei = xx[7]*1e9;
    const Double_t sEei = xx[8]*1e9;
    const Double_t energyResol_A = xx[9];
    const Double_t energyResol_B = xx[10];
    const Double_t lumi = xx[11];
    const Double_t Nturns = xx[12];
    const Double_t omega = xx[13];
    const Double_t thetaIn = xx[14];
    const Double_t maxAngle = xx[15];
    const Double_t miscalE_scale = xx[16];
    const Double_t scale2 = xx[17];
    const Double_t nExp = xx[18];
    const Double_t Z = xx[19];
    const Double_t scale3 = xx[20];
    const Double_t nBGExp = xx[21];
    const Double_t scale4 = xx[22];
    
    double gamma = mEei/me;
    double beta = TMath::Sqrt(1-1/(gamma*gamma));
    double x0 = 2*gamma*omega/me*(1+beta*TMath::Cos(thetaIn));
    double ymax = x0/(2*gamma*gamma*(1-beta) + x0*(1+TMath::Cos(thetaIn))/(1+beta*TMath::Cos(thetaIn)));
    double ymin = x0/(x0+2*gamma*gamma*(1-beta*TMath::Cos(maxAngle)));
    
    double epsilon = std::numeric_limits<double>::epsilon();
    
    // store lut for current mEei value
    if (abs(mEei-_curEei)>2*epsilon*mEei) {
        _curEei = mEei;
        _curEnergyResol_A = energyResol_A;
        _curEnergyResol_B = energyResol_B;
        _curMiscalE_scale = miscalE_scale;
        _curZ = Z;
        double gamma = _curEei/me;
        double beta = TMath::Sqrt(1-1/(gamma*gamma));
        double x0 = 2*gamma*omega/me*(1+beta*TMath::Cos(thetaIn));
        double ymax = x0/(2*gamma*gamma*(1-beta) + x0*(1+TMath::Cos(thetaIn))/(1+beta*TMath::Cos(thetaIn)));
        double ymin = x0/(x0+2*gamma*gamma*(1-beta*TMath::Cos(maxAngle)));
        
        fillLUT(x0,ymin,ymax,Z);
        fillLUTconvolE(x0,ymin,ymax,Z);
        fillLUTbins();
    }
    else if (abs(energyResol_A-_curEnergyResol_A)>(2*epsilon*energyResol_A) || abs(energyResol_B-_curEnergyResol_B)>(2*epsilon*energyResol_B)) {
        _curEnergyResol_A = energyResol_A;
        _curEnergyResol_B = energyResol_B;
        _curMiscalE_scale = miscalE_scale;
        _curZ = Z;
        fillLUTconvolE(x0,ymin,ymax,Z);
        fillLUTbins();
    }
    else if (abs(miscalE_scale-_curMiscalE_scale)>(2*epsilon*miscalE_scale)) {
        _curMiscalE_scale = miscalE_scale;
        _curZ = Z;
        //cout <<_curMiscalE_scale << endl;
        fillLUTbins();
    }
    else if (abs(Z-_curZ)>2*epsilon*Z) {
        _curZ = Z;
        fillLUTbinsBeamGas();
    }
    
    // init chi2
    double ML = 0;
    for (unsigned int k=0;k<_nBins;k++) {
        //retrieve current data point
        double hval =(hEg->GetBinContent(k+1));
        double func = functionEval(k,scale,scale2,Pz,PLasCirc,Nturns,x0,nExp,scale3,nBGExp,Z,scale4);

        if( hval>0 && func>0) {
            double val= func-hval*(1-TMath::Log(hval/func));
            if(k>_chi2binMin)
                ML+=val;
        }
    }
    
    return ML;
}


void generateData(TString filename,unsigned long seed=0,bool matchNGen=true,bool isNotToy=true,bool firstEvent=true,bool beamGasOnly=false) {
    
    // at LTL076
    /*double alphaX_ = -2.0120;//homogenous to 1
    double betaX_ = 5.10797;//m
    double emitX_ = 4.49E-9;//mmmrad
    double etaX_ = .13030;//m
    double etapX_ = .04644;//unit TBC
    double alphaY_ = 17.5537;
    double betaY_ = 120.656;
    double emitY_ = 2.8E-13;//mmmrad
    double etaY_ = 8.3E-10;//unit m
    double etapY_ = -1.E-10;//unit TBC*/
    // at before BLA2LE
    // be careful these are only approximate values (averages of nearby points).
    double alphaX_ = -8.7163;//homogenous to 1
    double betaX_ = 96.4621;//m
    double emitX_ = 4.49E-9;//mrad
    double etaX_ = -0.08333;//m
    double etapX_ = -0.0035;//unit TBC
    double alphaY_ = 9.4502;
    double betaY_ = 127.0947;
    double emitY_ = 4.5e-11;//mrad
    double etaY_ = -1.1e-09;//unit m
    double etapY_ = 6.8e-11;//unit TBC
    
    // remove beam sizes
   /* emitX_ = 0;//mmmrad
    etaX_ = 0;//m
    etapX_ = 0;//unit TBC
    emitY_ = 0;//mmmrad
    etaY_ = 0;//unit m
    etapY_ = 0;//unit TBC*/
    
    //misalignments
    double dx_=0e-3;
    double dy_=0e-3;
    double dxp_=0.0e-3;
    double dyp_=0.0e-3;
    
    //miscalibration scale
    double miscalE_scale_ = 1.;
   
    // e-beam paramters
    double mEei_ = 7e9; //eV
    double sEei_ = mEei_*6.3e-4; //eV
    std::vector<double> se_;
    se_.push_back(TMath::Sqrt(emitX_*betaX_+TMath::Power(etaX_*sEei_/mEei_,2))); se_.push_back(TMath::Sqrt(emitY_*betaY_+TMath::Power(etaY_*sEei_/mEei_,2))); se_.push_back(5e-3);
    unsigned int Nb_ = 1; //number of bunches accumulated (1=bunch/bunch measurement)
    double f_ = 1; //reprate accumulation, 1=no rep rate
    double Ne_ = 10e-9/TMath::Qe(); //number of electrons
    double Pz_ = 0.7;
    double Pt_ = 0;
    double phiElecPol_ = TMath::Pi()/2;
    
    //backgrounds
    double beamgasZ_ = 2.5; //7 may be legitimate from email discussion, 2.5 from paper.
    double Pressure_ = 5e-8; //magnified to debug the fit first. Must be set to 1e-7 or less. //mbar to Pascal (SI) = *100
    double beamgasL_ = 20;
    double Temperature_ = 300; //K
    double Bmag_ = 1; //T
    double Lmag_ = 1; //m

    //laser setup parameters
    double PLasCirc_ = -1; //laser helicity
    double PLasLin_ = 0;
    double phiLasPol_ = 0;
    std::vector<double> sL_;
    sL_.push_back(0.5e-3); sL_.push_back(0.5e-3); sL_.push_back(5e-12*TMath::C());
    double lambda_ = 515e-9;
    double omega_ = TMath::H()*TMath::C()/(TMath::Qe()*lambda_);
    double power_ = 5;//Watt
    double frep_ = 250e6;//Hz
    double EL_ = power_/frep_; // laser pulse energy in J
    double nL_ = EL_/(TMath::Qe()*omega_);
    
    // detector
    double L_=13;//meters
    double duration_=60*25;// sec
    double Tc_=10e-6;//revolution period, sec.
    unsigned int Nturns_ = duration_/Tc_;
    double crystalSize_=2.5e-2;
    double energyResol_A_=10.;// in percents //0.1;
    double energyResol_B_=1.;
    double maxAngle_=crystalSize_/(2*L_);
   
    // calculated interaction stuff
    double thetaIn_ = TMath::DegToRad()*7; //rad
    double phiIn_ = TMath::DegToRad()*0.; //rad
    double lumi_ = lumi(se_[0],se_[1],se_[2],Ne_,sL_[0],sL_[1],sL_[2],nL_,thetaIn_);
    unsigned int nGen_ = 10000000;
    double gam = mEei_/me;
    double bet = TMath::Sqrt(1-1/(gam*gam));
    double x0_ = 2*gam*omega_/me*(1+bet*TMath::Cos(thetaIn_));
    double xsecTot_=xsecTot(x0_,Pz_,PLasCirc_);
    double nExp_ = lumi_*xsecTot(x0_,Pz_,PLasCirc_);
    double nSRexp_ = Ne_*nSRtot(mEei_,Bmag_,Lmag_);
    double nBGexp_ = Ne_*nBGtot(beamgasL_,Pressure_,Temperature_,beamgasZ_,mEei_);
   
    //MC
    double xpos_ = 0;
    double xp_ = 0;
    double ypos_ = 0;
    double yp_ = 0;
    double xD_ = 0;
    double yD_ = 0;
    double zpos_ = 0;
    double Eei_ = 0; //eV
    double gamma_ = 0;
    double beta_ = 0;
    double x_ = 0;
    double ymax_ = 0;
    double ymin_ = 0;
    double xsecMax_ = 0;
    unsigned int nPhotons_ = 0;
    unsigned int nBGPhotons_ = 0;
    
    double Eg_ = 0;
    double phi_ = 0;
    double cosTheta_=0;
    double theta_=0;
    double resolE_=0;
    double Eg_meas_=0;
    double Eph_[5]={-1.,-1.,-1.,-1.,-1.};
    double Eeout_[5] = {-1.,-1.,-1.,-1.,-1.};
    double Pxeout_[5] = {0.,0.,0.,0.,0.};
    double Pyeout_[5] = {0.,0.,0.,0.,0.};
    double Pzeout_[5] = {0.,0.,0.,0.,0.};
    
    TRandom2 rand;
    rand.SetSeed(seed);
    
    TFile* file = NULL;

    if (isNotToy || firstEvent) {
        // store params
        file = new TFile(filename,"recreate");
    }
    
    TTree *params = NULL;
    if (isNotToy || firstEvent) {
    params = new TTree("parElectrons","parElectrons");
    params->Branch("alphaX",&alphaX_,"alphaX/D");
        params->Branch("betaX",&betaX_,"betaX/D");
        params->Branch("emitX",&emitX_,"emitX/D");
        params->Branch("etaX",&etaX_,"etaX/D");
        params->Branch("etapX",&etapX_,"etapX/D");
        params->Branch("alphaY",&alphaY_,"alphaY/D");
        params->Branch("betaY",&betaY_,"betaY/D");
        params->Branch("emitY",&emitY_,"emitY/D");
        params->Branch("etaY",&etaY_,"etaY/D");
        params->Branch("etapY",&etapY_,"etapY/D");
        params->Branch("dX",&dx_,"dX/D");
        params->Branch("dY",&dy_,"dY/D");
        params->Branch("dXp",&dxp_,"dXp/D");
        params->Branch("dYp",&dyp_,"dYp/D");
        params->Branch("miscalE_scale",&miscalE_scale_,"miscalE_scale/D");
     params->Branch("meanEei",&mEei_,"meanEei/D");
       params->Branch("sigmaEei",&sEei_,"sigmaEei/D");
    params->Branch("se",&se_);
    params->Branch("Nb",&Nb_,"Nb/i");
    params->Branch("f",&f_,"f/D");
    params->Branch("Ne",&Ne_,"Ne/D");
    params->Branch("Pz",&Pz_,"Pz/D");
    params->Branch("Pt",&Pt_,"Pt/D");
    params->Branch("phiElecPol",&phiElecPol_,"phiElecPol/D");
    params->Fill();
    params->Write();
        
    params = new TTree("parBackgrounds","parBackgrounds");
    params->Branch("beamgasZ",&beamgasZ_,"beamgasZ/D");
    params->Branch("Pressure",&Pressure_,"Pressure/D");
    params->Branch("beamgasL",&beamgasL_,"beamgasL/D");
    params->Branch("Temperature",&Temperature_,"Temperature/D");
    params->Branch("Bmag",&Bmag_,"Bmag/D");
    params->Branch("Lmag",&Lmag_,"Lmag/D");
    params->Branch("nSRexp",&nSRexp_,"nSRexp/D");
    params->Branch("nBGexp",&nBGexp_,"nBGexp/D");
    params->Fill();
    params->Write();

    params = new TTree("parLaser","parLaser");
    params->Branch("PLasCirc",&PLasCirc_,"PLasCirc/D");
    params->Branch("PLasLin",&PLasLin_,"PLasLin/D");
    params->Branch("phiLasPol",&phiLasPol_,"phiLasPol/D");
    params->Branch("sL",&sL_);
    params->Branch("power",&power_,"power/D");
    params->Branch("frep",&frep_,"frep/D");
    params->Branch("nL",&nL_,"nL/D");
    params->Branch("EL",&EL_,"EL/D");
    params->Branch("lambda",&lambda_,"lambda/D");
    params->Branch("omega",&omega_,"omega/D");
    params->Fill();
    params->Write();
    
    params = new TTree("parDetector","parDetector");
    params->Branch("L",&L_,"L/D");
    params->Branch("duration",&duration_,"duration/D");
    params->Branch("Tc",&Tc_,"Tc/D");
    params->Branch("Nturns",&Nturns_,"Nturns/i");
    params->Branch("crystalSize",&crystalSize_,"crystalSize/D");
    params->Branch("energyResol_A",&energyResol_A_,"energyResol_A/D");
    params->Branch("energyResol_B",&energyResol_B_,"energyResol_B/D");
    params->Branch("maxAngle",&maxAngle_,"maxAngle/D");
    params->Fill();
    params->Write();
    
    params = new TTree("parInteraction","parInteeraction");
    params->Branch("thetaIn",&thetaIn_,"thetaIn/D");
    params->Branch("phiIn",&phiIn_,"phiIn/D");
    params->Branch("lumi",&lumi_,"lumi/D");
    params->Branch("nGen",&nGen_,"nGen/i");
    params->Branch("x0",&x0_,"x0/D");
    params->Branch("xsecTot",&xsecTot_,"xsecTot/D");
    params->Branch("nExp",&nExp_,"nExp/D");
    params->Branch("nTurns",&Nturns_,"nTurns/i");
    params->Fill();
    params->Write();
    }
    if (isNotToy) {
        params = new TTree("mc","mc");
        params->Branch("xpos",&xpos_,"xpos/D");
        params->Branch("xp",&xp_,"xp/D");
        params->Branch("ypos",&ypos_,"ypos/D");
        params->Branch("yp",&yp_,"yp/D");
        params->Branch("zpos",&zpos_,"zpos/D");
        params->Branch("xD",&xD_,"xD/D");
        params->Branch("yD",&yD_,"yD/D");
        params->Branch("Eg",&Eg_,"Eg/D");
        params->Branch("phi",&phi_,"phi/D");
        params->Branch("cosTheta",&cosTheta_,"cosTheta/D");
        params->Branch("theta",&theta_,"theta/D");
        params->Branch("resolE",&resolE_,"resolE/D");
        params->Branch("Eg_meas",&Eg_meas_,"Eg_meas/D");
        params->Branch("Eei",&Eei_,"Eei/D");
        params->Branch("gamma",&gamma_,"gamma/D");
        params->Branch("beta",&beta_,"beta/D");
        params->Branch("x",&x_,"x/D");
        params->Branch("ymax",&ymax_,"ymax/D");
        params->Branch("ymin",&ymin_,"ymin/D");
        params->Branch("xsecMax",&xsecMax_,"xsecMax/D");
        params->Branch("nPhotons",&nPhotons_,"nPhotons/i");
        params->Branch("nBGPhotons",&nBGPhotons_,"nBGPhotons/i");
        params->Branch("Eph",Eph_,"Eph[5]/D");
        params->Branch("Eeout",Eeout_,"Eeout[5]/D");
        params->Branch("Pxeout",Pxeout_,"Pxeout[5]/D");
        params->Branch("Pyeout",Pyeout_,"Pyeout[5]/D");
        params->Branch("Pzeout",Pzeout_,"Pzeout[5]/D");
    }
    else if(file!=NULL)
        file->Close();
    
    if (!isNotToy) {
        if (firstEvent)
            hEg = new TH1D("hEg","",_nBins,_Egmin,_Egmax);
        else
            hEg->Reset();
    }
    
    //generate fixed number of events
    if(matchNGen) {
     for (unsigned int k =0;k<nGen_;k++) {
         
         Eei_ = rand.Gaus(mEei_,sEei_);
         gamma_ = Eei_/me;
         beta_ = TMath::Sqrt(1-1/(gamma_*gamma_));
         // we will use the approxiamte formula from ginzburg paper,
         // since it was checked that it is valid at SUperKEKB within 1e-5
         // (max amplitude of deviation within the range under consideration)
         x_ = 2*gamma_*omega_/me*(1+beta_*TMath::Cos(thetaIn_));
         ymax_ = x_/(2*gamma_*gamma_*(1-beta_) + x_*(1+TMath::Cos(thetaIn_))/(1+beta_*TMath::Cos(thetaIn_)));
         ymin_ = x_/(x_+2*gamma_*gamma_*(1-beta_*TMath::Cos(maxAngle_)));
         // i believe that the max cross-section appears when Pz*PLasCirc=-1 and
         // other polar params are vanishing.
         xsecMax_ = xsec(x_,ymax_,0,1,0,0,0,-1,0);
         
         
         double phi1 = rand.Rndm()*2*TMath::Pi();
         double phi2 = rand.Rndm()*2*TMath::Pi();
         double u1 = rand.Exp(1.);
         double u2 = rand.Exp(1.);
         xpos_ = TMath::Sqrt(2*u1*emitX_*betaX_)*TMath::Cos(phi1) + etaX_*(Eei_/mEei_-1);
         ypos_ = TMath::Sqrt(2*u2*emitY_*betaY_)*TMath::Cos(phi2) + etaY_*(Eei_/mEei_-1);
         xp_ = -TMath::Sqrt(2*u1*emitX_/betaX_)*(alphaX_*TMath::Cos(phi1)+TMath::Sin(phi1))+ etapX_*(Eei_/mEei_-1);
         yp_ = -TMath::Sqrt(2*u2*emitY_/betaY_)*(alphaY_*TMath::Cos(phi2)+TMath::Sin(phi2))+ etapY_*(Eei_/mEei_-1);
         zpos_ = rand.Gaus(0,se_[2]);
         
         double y = rand.Rndm()*ymax_;
         Eg_ = y*Eei_;
         phi_ = rand.Rndm()*2*TMath::Pi();
         double xsec_rnd=rand.Rndm()*xsecMax_;
         double xsec_calc = xsec(x_,y,phi_,Pz_,Pt_,phiElecPol_,PLasLin_,PLasCirc_,phiLasPol_);
         
         if (beamGasOnly) {
             y = rand.Rndm()*(1.-0.1e9/Eei_)+0.1e9/Eei_;
             Eg_ = y*Eei_;
             xsecMax_ =xsecBeamGas(0.1e9/Eei_,beamgasZ_);
             xsec_rnd = rand.Rndm()*xsecMax_;
             xsec_calc = xsecBeamGas(y,beamgasZ_);
         }
         
        if (xsec_rnd<xsec_calc) {
            if( beamGasOnly ) {
                resolE_=resolution(Eg_,energyResol_A_,energyResol_B_);
                Eg_meas_=miscalE_scale_*(Eg_+rand.Gaus(0,resolE_));
                
                if (Eg_meas_>0) {
                    if(isNotToy)
                        params->Fill();
                    else
                        hEg->Fill(Eg_meas_);
                }
                else
                    k--;
            }
            else {
                cosTheta_=1/beta_*(1-x_*(1-y)/(2*gamma_*gamma_*y));
                theta_ = TMath::ACos(cosTheta_);
                
                xD_  = dx_+ xpos_ + TMath::Tan(dxp_+xp_)*(L_-zpos_) +  TMath::Cos(phi_)*TMath::Tan(theta_)*(L_-zpos_);
                yD_  = dy_+ ypos_ + TMath::Tan(dyp_+yp_)*(L_-zpos_) +  TMath::Sin(phi_)*TMath::Tan(theta_)*(L_-zpos_);
                
                if ( xD_<crystalSize_/2. && xD_>(-crystalSize_/2.) && yD_<crystalSize_/2. && yD_>(-crystalSize_/2.)) {
                    resolE_=resolution(Eg_,energyResol_A_,energyResol_B_);
                    Eg_meas_=miscalE_scale_*(Eg_+rand.Gaus(0,resolE_));
                    
                    if (Eg_meas_>0) {
                        if(isNotToy)
                            params->Fill();
                        else
                            hEg->Fill(Eg_meas_);
                    }
                    else
                        k--;
                }
                else
                    k--;
            }
        }
        else
            k--;
        if (xsec_calc>xsecMax_) {
            cout << " ERROR: xsecMax is not found to be the actual max" << endl;
            break;
        }
    }
    }
    else {
        //generate according to asusmesing 1 event per turn
        for (unsigned int k=0;k<Nturns_;k++) {
            
            Eg_=0.;
            nPhotons_ = rand.Poisson(nExp_);
            if (nPhotons_>2)
                nPhotons_ = 2;
            //nPhotons_ = 1;
            //nPhotons_ = 0;
            if( beamGasOnly)
                nPhotons_ = 0;
            
            for (int kph=0;kph<5;kph++) {
                Eph_[kph]=-1;
                Eeout_[kph]=-1;
                Pxeout_[kph] = 0.;
                Pyeout_[kph] = 0.;
                Pzeout_[kph] = 0.;
            }
            for (int kph=0;kph<nPhotons_;kph++) {
                
                Eei_ = rand.Gaus(mEei_,sEei_);
                gamma_ = Eei_/me;
                beta_ = TMath::Sqrt(1-1/(gamma_*gamma_));
                
                // we will use the approxiamte formula from ginzburg paper,
                // since it was checked that it is valid at SUperKEKB within 1e-5
                // (max amplitude of deviation within the range under consideration)
                x_ = 2*gamma_*omega_/me*(1+beta_*TMath::Cos(thetaIn_));
                ymax_ = x_/(2*gamma_*gamma_*(1-beta_) + x_*(1+TMath::Cos(thetaIn_))/(1+beta_*TMath::Cos(thetaIn_)));
                ymin_ = x_/(x_+2*gamma_*gamma_*(1-beta_*TMath::Cos(maxAngle_)));
                // i believe that the max cross-section appears when Pz*PLasCirc=-1 and
                // other polar params are vanishing.
                xsecMax_ = xsec(x_,ymax_,0,1,0,0,0,-1,0);
            
                double phi1 = rand.Rndm()*2*TMath::Pi();
                double phi2 = rand.Rndm()*2*TMath::Pi();
                double u1 = rand.Exp(1.);
                double u2 = rand.Exp(1.);
                xpos_ = TMath::Sqrt(2*u1*emitX_*betaX_)*TMath::Cos(phi1) + etaX_*(Eei_/mEei_-1);
                ypos_ = TMath::Sqrt(2*u2*emitY_*betaY_)*TMath::Cos(phi2) + etaY_*(Eei_/mEei_-1);
                xp_ = -TMath::Sqrt(2*u1*emitX_/betaX_)*(alphaX_*TMath::Cos(phi1)+TMath::Sin(phi1))+ etapX_*(Eei_/mEei_-1);
                yp_ = -TMath::Sqrt(2*u2*emitY_/betaY_)*(alphaY_*TMath::Cos(phi2)+TMath::Sin(phi2))+ etapY_*(Eei_/mEei_-1);
                zpos_ = rand.Gaus(0,se_[2]);
                
                double xsec_rnd=rand.Rndm()*xsecMax_;
                double y = rand.Rndm()*ymax_;
                phi_ = rand.Rndm()*2*TMath::Pi();
                double xsec_calc = xsec(x_,y,phi_,Pz_,Pt_,phiElecPol_,PLasLin_,PLasCirc_,phiLasPol_);
                if (xsec_calc>xsecMax_) {
                    cout << " ERROR: xsecMax is not found to be the actual max" << endl;
                    break;
                }
               /* while(xsec_rnd>xsec_calc) {
                        xsec_rnd=rand.Rndm()*xsecMax_;
                        y = rand.Rndm()*ymax_;
                        phi_ = rand.Rndm()*2*TMath::Pi();
                        xsec_calc = xsec(x_,y,phi_,Pz_,Pt_,phiElecPol_,PLasLin_,PLasCirc_,phiLasPol_);
                        if (xsec_calc>xsecMax_) {
                            cout << " ERROR: xsecMax is not found to be the actual max" << endl;
                            break;
                        }
                }*/
                if (xsec_rnd<xsec_calc) {
                    cosTheta_=1/beta_*(1-x_*(1-y)/(2*gamma_*gamma_*y));
                    theta_ = TMath::ACos(cosTheta_);
                    
                    xD_  = dx_+ xpos_ + TMath::Tan(dxp_+xp_)*(L_-zpos_) +  TMath::Cos(phi_)*TMath::Tan(theta_)*(L_-zpos_);
                    yD_  = dy_+ ypos_ + TMath::Tan(dyp_+yp_)*(L_-zpos_) +  TMath::Sin(phi_)*TMath::Tan(theta_)*(L_-zpos_);
                    
                    //if ( xD_<crystalSize_/2. && xD_>(-crystalSize_/2.) && yD_<crystalSize_/2. && yD_>(-crystalSize_/2.)) {
                    if ( sqrt(xD_*xD_+yD_*yD_)<crystalSize_/2.) {
                        Eg_ += y*Eei_;
                    }
                    
                    if(kph<5) {//avoid crash
                        Eph_[kph] = y*Eei_;
                        Eeout_[kph] = Eei_-Eph_[kph]-omega_;
                        double phiout =rand.Rndm()*2*TMath::Pi();
                        Pxeout_[kph] = TMath::Sqrt(Eei_*Eei_-me*me)*TMath::Sin(xp_)-omega_*TMath::Sin(thetaIn_)-Eph_[kph]*TMath::Sin(theta_)*TMath::Cos(phiout);
                        Pyeout_[kph] = TMath::Sqrt(Eei_*Eei_-me*me)*TMath::Sin(yp_)-Eph_[kph]*TMath::Sin(theta_)*TMath::Sin(phiout);
                        Pzeout_[kph] = TMath::Sqrt(Eeout_[kph]*Eeout_[kph]-me*me-Pxeout_[kph]*Pxeout_[kph]-Pyeout_[kph]*Pyeout_[kph]);
                    }
                }
                else
                    kph--;
            }
            
            // add background contributions
            /*//Synchrotron radiation
            double EgenCutOFF = 1e6;
            double nSRPhotons_ = rand.Poisson(nSRexp_);
            for (int kph=0;kph<nSRPhotons_;kph++) {
                double y = (rand.Rndm()*(_Egmax-EgenCutOFF)+EgenCutOFF)/mEei_;
                double nSRcalc = Ne_*nSR(y,gamma_,mEei_,Bmag_,Lmag_);
                double nSRrand = rand.Rndm()*nSR(EgenCutOFF/mEei_,gamma_,mEei_,Bmag_,Lmag_);
                if (nSRrand<nSRcalc) {
                    Eg_ += y*mEei_;
                }
                else
                    kph--;
            }*/
            
            // beam gas
            nBGPhotons_ = rand.Poisson(nBGexp_);
            //if (nBGPhotons_>1)
            //    nBGPhotons_ = 1;
            double Afact=6.1; //has been empirically obtained with mathematica
            //int nTrials=0;
            //int nKept=0;
            for (int kph=0;kph<nBGPhotons_;kph++) {
                double Xrnd = rand.Rndm();
                double etaMin=TMath::Log(_beamGasEMinCutOff/mEei_);
                double eta = Afact - sqrt(Afact*Afact + (1-Xrnd)*(etaMin*etaMin- 2*Afact*etaMin));
                double xsec_rnd = rand.Rndm()*((Afact-eta));
                double y = TMath::Exp(eta);
                double xsec_calc = TMath::Log(xsecBeamGas(y,beamgasZ_))-TMath::Log(4/*alpha*re*re*/);
                if (xsec_calc>((Afact-eta)))
                    cout << "ERROR " << eta << " " << ((Afact-eta)) << " " << xsec_calc << endl;
                
                /*double y = rand.Rndm()*(1.-_beamGasEMinCutOff/mEei_)+_beamGasEMinCutOff/mEei_;
                double xsec_rnd = rand.Rndm()*xsecBeamGas(_beamGasEMinCutOff/Eei_,beamgasZ_);
                double xsec_calc = xsecBeamGas(y,beamgasZ_);*/
                
                if (xsec_rnd<xsec_calc) {
                    Eg_ += y*mEei_;
                    //nKept++;
                }
                else {
                    kph--;
                }
                //nTrials++;
                
            }
            /*if( nTrials>0)
                cout << "event " << k << " " << (double) ((double) nKept)/((double) nTrials) << endl;*/
            
            resolE_=resolution(Eg_,energyResol_A_,energyResol_B_);
            Eg_meas_= miscalE_scale_*(Eg_+rand.Gaus(0,resolE_));
            if (Eg_meas_>0) {
                if(isNotToy)
                    params->Fill();
                else {
                    hEg->Fill(Eg_meas_);
                }
            }
        }
    }
    
    if(isNotToy) {
        params->Write();
        file->Close();
    }
    
}

float inline maxGCC(ROOT::Math::Minimizer* min) {
    float maxGCC=0.;
    for (unsigned int k=0;k<17;k++)
        if( !min->IsFixedVariable(k))
            maxGCC = maxGCC>min->GlobalCC(k) ? maxGCC : min->GlobalCC(k);
    return maxGCC;
}

void writeElectronOutput(TString filename,bool doTransport = false) {
    
    TFile * file = new TFile(filename,"read");
    
    //params
    double xGen_ = 0;
    double xMeas_ = 0;
    double yGen_ = 0;
    double yMeas_ = 0;
    double px_[5] = {0.,0.,0.,0.,0.};
    double py_[5] = {0.,0.,0.,0.,0.};
    double pz_[5] ={0.,0.,0.,0.,0.};
    double E_[5] = {0.,0.,0.,0.,0.};
    double Eph_[5] = {-1.,-1.,-1.,-1.,-1.};
    double s_ = 124.072;
    
    //transport
   /* double m11 = 1.306137199348373;
    double m12 = 13.069393581750342;
    double m15 = 0.077255332449673;
    double m33 = -0.740635992130839;
    double m34 = 11.256306044072478;
    double m35 = 0;*/
    double m11 = 0.390655129182101;
     double m12 = 4.445759872751665;
     double m15 = 0.078449874292266;
     double m33 = -0.483070441902671;
     double m34 = 4.596981778720386;
     double m35 = 0;
    
    TTree* tree = (TTree*) file->Get("parElectrons");
    tree->GetEntry(0);
    double mEei_gen = (double) tree->GetLeaf("meanEei")->GetValue();
    double Pz_gen = (double) tree->GetLeaf("Pz")->GetValue();
    
    // get some key parameters
    TTree* mc = (TTree*) file->Get("mc");
    mc->SetBranchAddress("xpos",&xGen_);
    mc->SetBranchAddress("ypos",&yGen_);
    mc->SetBranchAddress("Pxeout",&px_);
    mc->SetBranchAddress("Pyeout",&py_);
    mc->SetBranchAddress("Pzeout",&pz_);
    mc->SetBranchAddress("Eeout",&E_);
    mc->SetBranchAddress("Eph",&Eph_);
    
    //open file for writing
    TString fName="generatedElectrons_Pz"+TString::Itoa(100*Pz_gen,10)+"prcent";
    if(doTransport)
        fName += "_detector";
    fName += ".txt";
    std::string fNamestr(fName.Data());
    ofstream fw(fNamestr, std::ofstream::out);
    //check if file was successfully opened for writing
    if (fw.is_open())
    {
        fw << "x_gen" << " " << "y_gen" << " " << "s_gen" << " " << "px [GeV]" << " " << "py [GeV]" << " " << "pz [GeV]" << " " << "E [GeV]" << "\n";
        //loop and write
        long int nEvents= mc->GetEntries();
        for (int k=0;k<nEvents;k++) {
            mc->GetEntry(k);
            for (int kP=0;kP<5;kP++) {
                if (Eph_[kP]>0) {
                    
                    if(doTransport) {
                        xMeas_ = m11*xGen_+m12*px_[kP]/sqrt(pz_[kP]*pz_[kP]+py_[kP]*py_[kP]+px_[kP]*px_[kP])+m15*(E_[kP]/mEei_gen-1);
                        yMeas_ = m33*yGen_+m34*px_[kP]/sqrt(pz_[kP]*pz_[kP]+py_[kP]*py_[kP]+px_[kP]*px_[kP])+m35*(E_[kP]/mEei_gen-1);
                        //store
                        fw << xMeas_ << " " << yMeas_ << " " << s_ << " " << px_[kP] << " " << py_[kP] << " " << pz_[kP] << " " << E_[kP] << "\n";
                    }
                    else {
                        //store
                        fw << xGen_ << " " << yGen_ << " " << s_ << " " << px_[kP] << " " << py_[kP] << " " << pz_[kP] << " " << E_[kP] << "\n";
                    }
                }
            }
        }
        fw.close();
    }
    else
        cout << "Problem with opening file";
    
}

void fitData(TString filename,TH1D *hFun=NULL,ROOT::Math::Minimizer* min=NULL,bool useNgen=true,bool isNotToy=true,bool isFirstEvent=true,bool doScan=false, bool beamGasOnly=false) {
    
    TFile * file = new TFile(filename,"read");
    // get some key parameters
    TTree* tree = (TTree*) file->Get("parElectrons");
    tree->GetEntry(0);
    double mEei_gen = (double) tree->GetLeaf("meanEei")->GetValue();
    double sEei_gen = (double) tree->GetLeaf("sigmaEei")->GetValue();
    double Pz_gen = (double) tree->GetLeaf("Pz")->GetValue();
    double Pt_gen = (double) tree->GetLeaf("Pt")->GetValue();
    double phiElecPol_gen = (double) tree->GetLeaf("phiElecPol")->GetValue();
    double miscalE_scale_gen = (double) tree->GetLeaf("miscalE_scale")->GetValue();
    tree = (TTree*) file->Get("parLaser");
    tree->GetEntry(0);
    double PLasCirc_gen = (double) tree->GetLeaf("PLasCirc")->GetValue();
    double PLasLin_gen = (double) tree->GetLeaf("PLasLin")->GetValue();
    double phiLasPol_gen = (double) tree->GetLeaf("phiLasPol")->GetValue();
    double omega_gen = (double) tree->GetLeaf("omega")->GetValue();
    tree = (TTree*) file->Get("parDetector");
    tree->GetEntry(0);
    double Nturns_gen = (double) tree->GetLeaf("Nturns")->GetValue();
    double energyResol_A_gen = (double) tree->GetLeaf("energyResol_A")->GetValue();
    double energyResol_B_gen = (double) tree->GetLeaf("energyResol_B")->GetValue();
    double maxAngle_gen = (double) tree->GetLeaf("maxAngle")->GetValue();
    tree = (TTree*) file->Get("parInteraction");
    tree->GetEntry(0);
    double nGen = (double) tree->GetLeaf("nGen")->GetValue();
    double lumi_gen = (double) tree->GetLeaf("lumi")->GetValue();
    double thetaIn_gen = (double) tree->GetLeaf("thetaIn")->GetValue();
    double nExp_gen = (double) tree->GetLeaf("nExp")->GetValue();
    tree = (TTree*) file->Get("parBackgrounds");
    tree->GetEntry(0);
    double Z_gen = (double) tree->GetLeaf("beamgasZ")->GetValue();
    double nBGExp_gen = (double) tree->GetLeaf("nBGexp")->GetValue();
    
    // retrieve the reference histogram
    if (isNotToy) {
        TTree* mc = (TTree*) file->Get("mc");
        hEg = new TH1D("hEg","hEg",_nBins,_Egmin,_Egmax);
        mc->Draw("Eg_meas>>hEg","","goff");
    }
    else {
        file->Close();
    }
    
    if(!min) {
        
        // choose minimizer
        // choose minimize
        //min =
        //  ROOT::Math::Factory::CreateMinimizer("Minuit2", "Migrad");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("Minuit2", "Simplex");
        //min =
        //          ROOT::Math::Factory::CreateMinimizer("Minuit2", "Combined");
        min =
                  ROOT::Math::Factory::CreateMinimizer("Minuit2", "Scan");
        //   ROOT::Math::Minimizer* min =
        //         ROOT::Math::Factory::CreateMinimizer("Minuit2", "Fumili");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "ConjugateFR");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "ConjugatePR");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "BFGS");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "BFGS2");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "SteepestDescent");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiFit", "");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLSimAn", "");
        
    }
    
    ROOT::Math::Functor f(&chi2,23);
    //ROOT::Math::Functor f(&ML,23);
    //min->SetErrorDef(0.5);
    
    min->Clear();

    min->SetFunction(f);
    
   // if(isFirstEvent) {
        min->SetMaxFunctionCalls(5000);
        min->SetMaxIterations(100000);
        min->SetStrategy(2);
        if (isNotToy)
            min->SetPrintLevel(5); // debug info
        else
            min->SetPrintLevel(1);
        min->SetValidError(true);

        // we want to have parameters not too large not too small
        // convert energies in Gev instead of eV
          
        // Set the free variables to be minimized
    if (beamGasOnly) {
        min->SetFixedVariable(0,"scale",0.);
        min->SetFixedVariable(1,"Pz",Pz_gen);
    }
    else {
        min->SetVariable(0,"scale",1.,0.0001);
        min->SetVariable(1,"Pz",0,0.001);
    }
        min->SetFixedVariable(2,"Pt",Pt_gen);
        min->SetFixedVariable(3,"phiElecPol",phiElecPol_gen);
        min->SetFixedVariable(4,"PLasLin",PLasLin_gen);
        min->SetFixedVariable(5,"PLasCirc",PLasCirc_gen);
        min->SetFixedVariable(6,"phiLasPol",phiLasPol_gen);
        min->SetFixedVariable(7,"Eei",mEei_gen/1e9);
        ///min->SetVariable(7,"Eei",(mEei_gen-0.3e9)/1e9,0.000001);
        min->SetFixedVariable(8,"sEei",sEei_gen/1e9);
        min->SetFixedVariable(9,"energyResol_A",energyResol_A_gen);
        //min->SetVariable(9,"energyResol_A",3.,1.); //percents units
        min->SetFixedVariable(10,"energyResol_B",energyResol_B_gen);
        ///min->SetVariable(10,"energyResol_B",0.003,0.0001);
        min->SetFixedVariable(11,"lumi",lumi_gen);
        if (useNgen)
            min->SetFixedVariable(12,"Nturns",nGen);
        else
            min->SetFixedVariable(12,"Nturns",Nturns_gen);
        min->SetFixedVariable(13,"omega",omega_gen);
        min->SetFixedVariable(14,"thetaIn",thetaIn_gen);
        min->SetFixedVariable(15,"maxAngle",maxAngle_gen);
        min->SetFixedVariable(16,"miscalE_scale",miscalE_scale_gen);
        //min->SetVariable(16,"miscalE_scale",1.,0.5);
    if (beamGasOnly) {
        min->SetFixedVariable(17,"scale2",0.);
    }
    else {
        min->SetVariable(17,"scale2",1.,0.0001);
    }
        min->SetFixedVariable(18,"nExp",nExp_gen);
        //min->SetFixedVariable(19,"beamgasZ",Z_gen*1.01);
        min->SetVariable(19,"beamgasZ",4.,2);
        min->SetVariable(20,"scale3",1.,0.5);
        //min->SetFixedVariable(20,"scale3",1.);
        min->SetFixedVariable(21,"nBGExp",nBGExp_gen);
        //min->SetVariable(22,"scale4",10.,0.0001);
        min->SetFixedVariable(22,"scale4",1.);

        // set parameter ranges
        min->SetVariableLimits(0,0.001,1000);
        min->SetVariableLimits(1,-1.5,1.5);
        min->SetVariableLimits(9,0.3,15.);
        min->SetVariableLimits(10,0.001,0.05);
        min->SetVariableLimits(7,(mEei_gen-1e9)/1e9,(mEei_gen+1e9)/1e9);
        min->SetVariableLimits(16,0.5,1.5);
         min->SetVariableLimits(17,0.001,1000.);
        min->SetVariableLimits(19,0.1,7.5);
        min->SetVariableLimits(20,0.,100000);
        min->SetVariableLimits(22,0.001,1000);

        if ( ((!min->IsFixedVariable(7)) && (!min->IsFixedVariable(16))))
          min->SetTolerance(1);
        else if (!min->IsFixedVariable(18))
          min->SetTolerance(100);
        else
          min->SetTolerance(0.001);
    //}
    /*else {
        min->Clear();
        min->SetVariableValue(0,1.);
        min->SetVariableStepSize(0,0.0001);
        min->SetVariableValue(1,0.);
        min->SetVariableStepSize(1,0.001);
        min->SetVariableValue(17,1.);
        min->SetVariableStepSize(17,0.0001);
        min->SetVariableValue(20,1.);
        min->SetVariableStepSize(20,0.0001);
        min->SetVariableValue(22,1.);
        min->SetVariableStepSize(22,0.0001);
        
        const double* params = min->X();
        cout << params << endl;
        cout << " Scale parameters " << params[20] << " " << params[22] << endl;
    //}*/
    
    if (isFirstEvent) {
        _curEei = 0.;
        _curEnergyResol_A = 0.;
        _curEnergyResol_B = 0.;
        _curMiscalE_scale = 0.;
        _curZ = 0.;
    }
    
    /*if (beamGasOnly && (!min->IsFixedVariable(19))) {
        unsigned int nstep0 = 10;
        double Zi0[nstep0];
        double chi20[nstep0];
        min->Scan(19,nstep0,Zi0,chi20,1,7.5);
        min->Minimize();
    }*/
    
    //const double* params = min->X();
    //cout << params << endl;
    //cout << " Scale parameters " << params[20] << " " << params[22] << endl;
    //minimize
    /*if ((!min->IsFixedVariable(19)) && (!min->IsFixedVariable(20) ) )  {
        min->SetFixedVariable(19,"beamgasZ",4.);
        min->Minimize();
        min->FixVariable(20);
        min->ReleaseVariable(19);
        min->SetVariableLimits(19,0.1,7.5);
        if (!min->IsFixedVariable(20))
            cout << "ERROR fixing variable" << endl;
        else {
            const double *fitres0 = min->X();
            unsigned int nstep0 = 30;
            double Z0[nstep0];
            double chi20[nstep0];
            min->Scan(19,nstep0,Z0,chi20,0.1,7.5);
            for (int k=0;k<nstep0;k++)
                cout << Z0[k] << " " << chi20[k] << endl;
            //min->Minimize();
            //min->ReleaseVariable(20);
            //min->Minimize();
        }
    }
    else {*/
        min->Minimize();
    //}
         
    //improve when needed
    const double *fitresErr0 = min->Errors();
    if ((!min->IsFixedVariable(7))  && fitresErr0[7]<1E-6) {
        const double *fitres0 = min->X();
        unsigned int nstep0 = 30;
        double Eei0[nstep0];
        double chi20[nstep0];
        min->Scan(7,nstep0,Eei0,chi20,fitres0[7]-0.01,fitres0[7]+0.01);
        min->Minimize();
    }
    if ( ((min->Status()>0 ||  maxGCC(min)>0.9) && (min->IsFixedVariable(7) || min->IsFixedVariable(16)))) {
        min->Minimize();
    }
    else if ( (min->Status()>0 ||  min->GlobalCC(0)>0.9 ||  min->GlobalCC(1)>0.9) && ( (!min->IsFixedVariable(7) && !min->IsFixedVariable(16)) || !min->IsFixedVariable(19)) ) {
        min->Hesse();
        min->Minimize();
    }
    min->Hesse();
    if ( ((min->Status()>0 ||  maxGCC(min)>0.9) && (min->IsFixedVariable(7) || min->IsFixedVariable(16))) ||
         ((min->Status()>1 ||  min->GlobalCC(0)>0.9 ||  min->GlobalCC(1)>0.9) && (!min->IsFixedVariable(7) && !min->IsFixedVariable(16))) ) {
        min->Minimize();
        min->Hesse();
    }
    
    /*//this can be used if some paramter scanning is required
    double best = 99999;
    const double* bestPars = min->X();
    if(min->CovMatrixStatus()>0) {
        best = min->MinValue();
    }
    
    // reoptimize at best point
    min->SetVariableValue(0,bestPars[0]);
    min->SetVariableValue(1,bestPars[1]);
    //min->SetVariableValue(9,0.05,0.15);
    //min->SetVariableValue(10,0.001,0.05);
    min->SetVariableValue(7,bestPars[3]);
    min->SetVariableValue(16,bestPars[4]);
    min->SetVariableStepSize(16,0.001);
    min->Minimize();
    
    // randomize the init parameters
    TRandom2 gene;
      for (int k =0;k<4;k++) {
          min->SetVariableValue(16,1+(2*gene.Rndm()-1.)*0.05);
          //minimize
          min->Minimize();
          
          if (min->CovMatrixStatus()>0 && min->MinValue()<best) {
              best =min->MinValue();
              bestPars = min->X();
          }
      }
*/
    
    //print covmat
    if (isNotToy) {
        TMatrixD covMatrix(min->NDim(), min->NDim());
        min->GetCovMatrix(covMatrix.GetMatrixArray());
        covMatrix.Print();
        TMatrixD hMatrix(min->NDim(), min->NDim());
        min->GetHessianMatrix(hMatrix.GetMatrixArray());
        hMatrix.Print();
    }
     
    //get fit result
    const double *fitres = min->X();
    if (!hFun)
        hFun = new TH1D();
    if (isNotToy || isFirstEvent) {
        hEg->Copy(*hFun);
        hFun->Reset();
    }
    else if (!isNotToy)
        hFun->Reset();
    
    double norm = 0;
    if (useNgen)
        norm=nGen;
    else
        norm=Nturns_gen;
    
    double gamma = fitres[7]*1e9/me;
    double beta = TMath::Sqrt(1-1/(gamma*gamma));
    double x0 = 2*gamma*fitres[13]/me*(1+beta*TMath::Cos(fitres[14]));
    
    for (unsigned int k=0;k<_nBins;k++) {
        //retrieve current data point
        double Eg = (double) (hEg->GetBinCenter(k+1));
        double dEg = (double) (hEg->GetBinWidth(k+1));
        double convol = functionEval(k,fitres[0],fitres[17],fitres[1],PLasCirc_gen,norm,x0,nExp_gen,fitres[20],nBGExp_gen,fitres[19],fitres[22]);
        
        hFun->SetBinContent(k+1,convol);
    }
    
    if (isNotToy) {
        file->ReOpen("update");
        TTree *tfitres = new TTree("fitResults","fitResults");
        tfitres->Branch("hEg","TH1D",&hEg,32000,0);
        tfitres->Branch("hEgFit","TH1D",&hFun,32000,0);
        tfitres->Fill();
        tfitres->Write();
    }
    
    if (isNotToy && doScan) {
        file->ReOpen("update");
        double Pz_[100];
        double Eei_[100];
        double chi2_[100];
        double miscalE_scale_[100];
        
        /*TTree *t = new TTree("scan","scan");
        t->Branch("Pz",Pz_,"Pz[100]/D");
        t->Branch("chi2",chi2_,"chi2[100]/D");
        unsigned int nstep=100;
        min->Scan(1,nstep,Pz_,chi2_,fitres[1]-0.0001,fitres[1]+0.0001);
        t->Fill();
        t->Write();*/
        
        /*TTree *t = new TTree("scanEei","scanEei");
        t->Branch("Eei",Eei_,"Eei[100]/D");
        t->Branch("chi2",chi2_,"chi2[100]/D");
        unsigned int nstep=100;
        min->Scan(7,nstep,Eei_,chi2_,fitres[7]-0.1,fitres[7]+0.1);
        t->Fill();
        t->Write();*/
        
        TTree *t = new TTree("scanMiscalE","scanMiscalE");
        t->Branch("miscalE_scale",miscalE_scale_,"miscalE_scale[100]/D");
        t->Branch("chi2",chi2_,"chi2[100]/D");
        unsigned int nstep=100;
        min->Scan(16,nstep,miscalE_scale_,chi2_,1.025,1.028);
        t->Fill();
        t->Write();
    }
    
    if (isNotToy)
        file->Close();
}

void toyMC(TString filename,unsigned int nToys,unsigned long seedShift=1000,bool beamGasOnly=false) {
    
     //toyMC values stored
       double chi2_=0;
       double scale_ = 0;
       double scale_error_=0;
       double scale2_ = 0;
       double scale2_error_=0;
       double Pz_=0;
       double Pz_error_=0;
    double Pz_error_up = 0;
    double Pz_error_down = 0;
        double miscalE_scale_=0;
        double miscalE_scale_error_=0;
       double Ee_=0;
       double Ee_error_=0;
      double energyResol_A_=0;
      double energyResol_A_error_=0;
       unsigned long seed_ = 0;
       int status_ = -9;
       TH1D* hFun_ = NULL;
     
     // choose minimizer
     // choose minimize
        ROOT::Math::Minimizer* min =
            ROOT::Math::Factory::CreateMinimizer("Minuit2", "Migrad");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("Minuit2", "Simplex");
       // ROOT::Math::Minimizer* min =
       //           ROOT::Math::Factory::CreateMinimizer("Minuit2", "Combined");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("Minuit2", "Scan");
        //   ROOT::Math::Minimizer* min =
         //         ROOT::Math::Factory::CreateMinimizer("Minuit2", "Fumili");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "ConjugateFR");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "ConjugatePR");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "BFGS");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "BFGS2");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiMin", "SteepestDescent");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLMultiFit", "");
        //   ROOT::Math::Minimizer* min =
        //          ROOT::Math::Factory::CreateMinimizer("GSLSimAn", "");
    
     
     // create the toyMC file
     TFile file(filename,"recreate");
      TTree *tfitres = new TTree("fitResults","fitResults");
      tfitres->Branch("hEg","TH1D",&hEg,32000,0);
      tfitres->Branch("hEgFit","TH1D",&hFun_,32000,0);
      tfitres->Branch("chi2",&chi2_,"chi2/D");
      tfitres->Branch("seed",&seed_,"seed/l");
      tfitres->Branch("status",&status_,"status/I");
      tfitres->Branch("scale2",&scale2_,"scale2/D");
      tfitres->Branch("scale2_err",&scale2_error_,"scale2_err/D");
      tfitres->Branch("scale",&scale_,"scale/D");
      tfitres->Branch("scale_err",&scale_error_,"scale_err/D");
      tfitres->Branch("miscalE_scale",&miscalE_scale_,"miscalE_scale/D");
      tfitres->Branch("miscalE_scale_err",&miscalE_scale_error_,"miscalE_scale_err/D");
      tfitres->Branch("energyResol_A",&energyResol_A_,"energyResol_A/D");
      tfitres->Branch("energyResol_A_err",&energyResol_A_error_,"energyResol_A_err/D");
      tfitres->Branch("Pz",&Pz_,"Pz/D");
      tfitres->Branch("Ee",&Ee_,"Ee/D");
      tfitres->Branch("Ee_err",&Ee_error_,"Ee_err/D");
      tfitres->Branch("Pz_err",&Pz_error_,"Pz_err/D");
      
    
      clock_t t1 = clock();
      clock_t t2 = clock();
        double time_spent_gen = 0;
        double time_spent_fit = 0;
          
      
     //run toy
      for (unsigned int k=0;k<nToys;k++) {
          seed_ = seedShift+k;
          t1 = clock();
          generateData(TString("paramsToy.root"),seed_,false,false,(bool) (k==0),beamGasOnly);
          t2 = clock();
          time_spent_gen += (double)(t2 - t1) / CLOCKS_PER_SEC;
          fitData(TString("paramsToy.root"),hFun_,min,false,false,(bool) (k==0),beamGasOnly);
          t1 = clock();
          time_spent_fit += (double)(t1 - t2) / CLOCKS_PER_SEC;
          const double *fitpar = min->X();
          const double *fitparerr = min->Errors();
          //min->GetMinosError(1,Pz_error_down,Pz_error_up);
          scale_ = fitpar[0];
          scale2_ = fitpar[17];
          Pz_ = fitpar[1];
          miscalE_scale_ = fitpar[16];
          Ee_ = fitpar[7];
          energyResol_A_ = fitpar[9];
          scale_error_ = fitparerr[0];
          scale2_error_ = fitparerr[17];
          Pz_error_ = fitparerr[1];
          miscalE_scale_error_ = fitparerr[16];
          Ee_error_ = fitparerr[7];
          energyResol_A_error_ = fitparerr[9];
          chi2_ = min->MinValue()/min->ErrorDef();
          status_ =  min->Status();
          file.cd();
          tfitres->Fill();
      }
      tfitres->Write();
      file.Close();
    
      cout << " Time spent by Algorithm in generation is " << time_spent_gen/nToys << " seconds per toy event in average" << endl;
      cout << " Time spent by Algorithm in fitting is " << time_spent_fit/nToys << " seconds per toy event in average" << endl;
}

void plots(TString filename,bool isNotToy=true) {
    
    // plot histograms
    TH1D* hEgFit=NULL;
    TH1D* hEg2=NULL;
    double chi2_=0;
    TFile file(filename,"read");
    TTree *tree = (TTree*)file.Get("fitResults");
    tree->SetBranchAddress("hEgFit",&hEgFit);
    tree->SetBranchAddress("hEg",&hEg2);
    if(!isNotToy) {
        tree->SetBranchAddress("chi2",&chi2_);
    }
    Long64_t nentries = tree->GetEntries();
    
    // draw fit results
    TCanvas *c=new TCanvas("c","fit result");
    TPad *pad1 = new TPad("pad1","pad1",0,0.2,1,1);
    TPad *pad2 = new TPad("pad2","pad2",0,0,1,0.19);
    pad1->SetBottomMargin(0.00001);
    pad1->SetBorderMode(0);
    pad2->SetTopMargin(0.00001);
    pad2->SetBottomMargin(0.1);
    pad2->SetBorderMode(0);
    pad1->Draw();
    pad2->Draw();
    TH1D* hRes = new TH1D();
    TString pltname="mc/Egfit";
    gStyle->SetOptStat(0);
    for (unsigned int k=0;k<nentries;k++) {
        tree->GetEntry(k);
        TString currname = pltname+"_"+TString::Itoa(k,10)+".png";
        pad1->cd();
        hEg2->Draw("E");
        hEgFit->Draw("same");
        pad2->cd();
        hEg2->Copy(*hRes);
        hRes->Add(hEgFit,-1);
        double chi2modified = 0;
        int nbinsmodified = 0;
        for (int kk=0;kk<hRes->GetNbinsX();kk++) {
            hRes->SetBinError(kk+1,hEg2->GetBinError(kk+1));
            if ((kk+1)>_chi2binMin && lutbins_0[kk+1]>0 && kk<(_nBins-1)) {
                chi2modified += pow(hRes->GetBinContent(kk+1)/hEg2->GetBinError(kk+1),2);
                nbinsmodified++;
            }
        }
        cout << "modified chi2 " << chi2modified << " nbinsmodified " << nbinsmodified<< endl;
        hRes->Draw("E");
        c->Update();
        c->Print(currname,".png");
        if (!isNotToy) {
            hEg2->Reset();
            hRes->Reset();
            hEgFit->Reset();
        }
    }
    
    if (!isNotToy) {
        // chi2 plot
        pltname="mc/chi2.png";
        TCanvas *c_chi2=new TCanvas("c_chi2","chi2");
        unsigned int nbins = 0;
        double min = 1000;
        double max = 0;
        for (unsigned int k=0;k<nentries;k++) {
            tree->GetEntry(k);
            if (k==0)
                nbins = hEg2->GetNbinsX();
            if (chi2_>max)
                max=chi2_;
            if (chi2_<min)
                min=chi2_;
        }
        TF1 fchi2("chi2pdf",chi2pdf,min*0.9,max*1.1, 2);
        double parChi2[2] = {(double) (nbins-2),(double) nentries};
        fchi2.SetParameters(parChi2);
        tree->Draw("chi2","","E");
        fchi2.Draw("same");
        c_chi2->Print(pltname,".png");
        
        // draw teh Pz pull
        gStyle->SetOptFit(1111);
        pltname="mc/Pz_pull.png";
        TCanvas *c_pz=new TCanvas("c_pz","Pz");
        TH1D* hPz = new TH1D("hPz","",100,-5,5);
        tree->Draw("(Pz-0.7)/Pz_err>>hPz","","E");
        hPz->Fit("gaus");
        c_pz->Print(pltname,".png");
        
        // draw teh Pz pull
        gStyle->SetOptFit(1111);
        pltname="mc/miscalE_scale_pull.png";
        TCanvas *c_miscal=new TCanvas("c_miscal","miscalE_scale");
        TH1D* hMiscalE = new TH1D("hMiscalE","",100,-5,5);
        tree->Draw("(miscalE_scale-1.03)/miscalE_scale_err>>hMiscalE","","E");
        hMiscalE->Fit("gaus");
        c_miscal->Print(pltname,".png");
        
        // draw teh scale pull
        //gStyle->SetOptFit(1111);
        /*pltname="mc/scale_pull.png";
        TCanvas *c_scale=new TCanvas("c_scale","scale");
        TH1D* hScale = new TH1D("hScale","",100,-5,5);
        tree->Draw("(scale-1)/scale_err>>hScale","","E");
        hScale->Fit("gaus");
        c_scale->Print(pltname,".png");
        */
    }
    
    file.Close();
}

void run_beamPars_noXSECLUT() {
    
    bool isToy = false;
    bool plotOnly = false;
    bool genOnly = false;
    bool beamGasOnly = true;
    
    //one shot
    if (isToy) {
        clock_t begin = clock();
        unsigned int nToys = 100;
        unsigned long seedShift = 1000;
        TString filename = "toyMCbeamParsbkg"+TString::Itoa(nToys,10)+"_i"+TString::Itoa(seedShift,10)+".root";
        if (!plotOnly) {
            toyMC(filename,nToys,seedShift,beamGasOnly);
            clock_t end = clock();
            double time_spent = (double)(end - begin) / CLOCKS_PER_SEC;
            cout << " Time spent by Algorithm is " << time_spent/nToys << " seconds per toy event in average" << endl;
        }
        plots(filename);
    }
    else {
        bool doScan = false;
        bool writeElectrons=false;
        unsigned long seed = 1000; //1045
        TString filename = "dataGenerate_beamPars_Pz0.7.root";
        TH1D* hFun_ = NULL;
        generateData(filename,seed,/*matchNGen*/false,/*isNotToy*/true,/*firstEvent*/true,beamGasOnly);
        if(writeElectrons)
            writeElectronOutput(filename,/*withTransport*/true);
        if (!genOnly) {
            fitData(filename,/**hFun*/NULL,/*ROOT::Math::Minimizer* min*/NULL,/*useNgen=*/false,/*isNotToy=*/true,/*isFirstEvent=*/true,/*doScan=*/doScan,beamGasOnly);
            plots(filename,/*isNotToy=*/true);
        }
    }
}
