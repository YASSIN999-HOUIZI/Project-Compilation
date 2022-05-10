%{
	  #include <stdio.h>
	  #include <string.h>
	  #include <stdlib.h>
    #include "syntaxe.h"
    extern int lineNumber;
    extern int local;
    extern int firstloc;
    extern void yyerror(const char * msg);
    extern void dicolocal();
    extern void affiche(int a,int b);
    extern int continst;
    
%}
%option noyywrap
entier [0-9]+
reel [0-9]+\.[0-9]+
crt (')([^\w]|[\w])?(')
ch_crt "\""[^\n"\""]*"\"" 
identif [a-zA-Z_][0-9a-zA-Z_]*
communline "//".*
commpluslignes [/][*][^*]*[*]+([^*/][^*]*[*]+)*[/]
%%
debut   {return DEBUT;}
fin     {return FIN;}
"="     {return AFFECT;}
"!="    {return DIFF;}
">="    {return SUP_E;}
"<="    {return INF_E;}
"=="    {return EGAL_EGAL;}
"&&"    {return ET;}
"||"    {return OU;}
".."    {return A;}
":"     {return DEUX_POINT;}
"++"    {return PLUS_PLUS;}
"--"    {return MOIN_MOIN;}
"+="    {return PLUS_EGAL;}
"-="    {return MOIN_EGAL;}
"/="    {return DIV_EGAL;}
"*="    {return MULT_EGAL;}
"%="    {return MODULO_EGAL;}
">"     {return SUP;}
"<"     {return INF;}
";"     {return PTVIRG;}
","     {return VIRG;}
"+"     {return PLUS;}
"-"     {return MOIN;}
"*"     {return MULT;}
"/"     {return DIV;}
"!"     {return NON;}
"%"     {return MODULO;}
"("     {return PARENT_O;}
")"     {return PARENT_F;}
"{"     {return AC_O;}
"}"     {return AC_F;}
"]"     {return CROCH_F;}
"["     {return CROCH_O;}
"."     {return POINT;}
".="    {return POINT_EGAL;}
Algorithme {return ALGO;}
retourne {return RETOURNE;}
si    {return SI;}
alors {return ALORS;}
sinon {return SINON;}
pour {return POUR;}
faire {return FAIRE;}
tantque {return TANTQUE;}
selonque {return SELONQUE;}
case {return CAS;}
defaut {return DEFAUT;}
de {return DE;}
repeter {return REPETER;}
ftq {return FINTANTQUE;}
fpour {return FINPOUR;}
fsq {return FINSELONQUE;}
fsi {return FINSI;}
afficher {return AFFICHER;}
lire {return LIRE;}

par {return PAR;}
jusqua {return JUSQUA;}

Entier|Reel|Caractere|booleen {strcpy(yylval.var1, yytext);return TYPE;}
Fonction {firstloc=1;local=0;affiche(continst,0);
            continst=0;dicolocal();return FONCTION;}
Vrai {return VRAI;}
Faux {return FAUX;}
arret {return ARRET;}
continue {return CONTINUE;}
var {strcpy(yylval.var1, yytext);return VARIABLE;}
conste {strcpy(yylval.var1, yytext);return CONSTANTE;}
Procedure {firstloc=1;local=0;affiche(continst,0);
            continst=0;dicolocal();return PROCEDURE;}
{entier}  {yylval.entier = atoi(yytext);return ENT;}
{reel}    {yylval.reel = atof(yytext);return REEL;}
{identif} {if(strlen(yytext)>31){yyerror("le max du nombre des carateres d'identif <30\n");exit(-1);}else {strcpy(yylval.var1, yytext);return IDENTIF;}}
{ch_crt}  {strcpy(yylval.var1,yytext);return CH_CRT;}
{crt}  {strcpy(yylval.var1,yytext);return CRT;}
{communline}  {}
{commpluslignes}    {}
[ \t] {}
[\n] {++lineNumber;}
. {return yytext[0];}
%%return 1;
