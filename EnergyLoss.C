#include <iostream> 
#include <TROOT.h>
#include <TFile.h>
#include <TTree.h>
#include <TH1.h>
#include <TH2.h>
#include <TCanvas.h>
#include <TGraph.h>
#include <TLegend.h>
#include <TStyle.h>
#include <TMath.h>
#include <TF2.h>
#include "constants.h"

double x_fun(double Ebeam, double Ephotons, double alpha_0)
{
  return (4*Ebeam*Ephotons*TMath::Cos(alpha_0/2.0))/(me*me);
}
/*
double y(double Ebeam, double Ephotons)
{
  return Ephotons/Ebeam;
}
*/
double r_xy(double x_fun, double y)
{
  return y/(x_fun*(1-y));
}

double N_ph(double Ephotons, double temp)
{
  return Ephotons*Ephotons/(TMath::Power(TMath::Pi(),2)*TMath::Power(hbarc,3)*(TMath::Exp(Ephotons/(kB*temp))-1));
}

double Ephotons_min(double y, double Ebeam, double alpha_0)
{
  return y*me*me/(4*(1-y)*Ebeam*TMath::Power(TMath::Cos(alpha_0/2),2));
}

double compton_xsec(double y, double x_fun, double r)
{
  return (2*TMath::Pi()*re*re/x_fun)*(1/(1-y)+1-y-4*r*(1-r));
}

Double_t integrand(Double_t* x,Double_t *par){
  Double_t sigma_c = par[0];
  Double_t alpha_0 = par[1];
  Double_t temp = par[2];
  

  return sigma_c*(1+TMath::Cos(alpha_0/2))*TMath::Power(x[0],2)/(TMath::Power(TMath::Pi(),2)*TMath::Power(hbarc,3)*(TMath::Exp(x[0]/(kB*temp))-1));
}

double integral(double y,double Ebeam, double Ephotons, double alpha0, double tempT)
{
//  double x0 = x_fun(Ebeam,Ephotons,alpha0); //the y variable is related to the elements after the interaction 
  double r0 = r_xy(x0,y);
//  double N0 = N_ph(Ephotons,temp);
  double omega_min = Ephotons_min(y,Ebeam,alpha0);
  double sigma = compton_xsec(y,x0,r0);

  TF1* function = new TF1("integrand",integrand,0,10);

  function->SetParameters(sigma,alpha0,tempT);

  Double_t result= function->Integral(omega_min,TMath::Infinity());
 
  return result;
}

double dN_dy(double N_p, double L,double y,double Ebeam, double Ephotons, double alpha0, double tempT)
{
  return N_p*L/4*integral(y,Ebeam,Ephotons,alpha_0,temp);  
} 

int EnergyLoss()
{
  double N_p=1e12;
  double L=5000;
  double Ebeam = ;
  double Ephoton = 0.0;
  double alpha_0 = 0.0;
  double temp = 300;


  dN_dy();

  return 0;
}
