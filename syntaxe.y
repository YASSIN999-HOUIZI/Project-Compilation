%{
   #include <stdio.h>
   #include <stdlib.h>
   #include <string.h>
   #include "syntaxe.h"
   #include "vars.h"
   extern FILE* yyin; //file pointer by default points to terminal
   int yylex(void); // defini dans progL.cpp, utilise par yyparse()
   void yyerror(const char * msg);
   int isToken(char *s, char t[][16]);
   int isDeclared(char *s);
   void createIdentif(char *s);
   void isUsable(char *s);
   void identifTest(int tab,char *s,char t[][16]);
   vars *Creation(char *s);
   void Insertvar(char *s,int tab);
   int Chercher(char *s);
   int cherche(char *s);
  void returntype(char *s);
   void afficher();
   void affiche(int a,int b);
   void affect_type_fun(int tab,char s[31],char type[20]);
   void dicolocal();
   void dicoglobal();
   vars *CHERCHE(char *s);
  void affect_type(int a,char s[20]);
  void affect_indix(char *s,int a,int b);
  fonction *Creationfon(char *s);
  void fonctionTest(int proc,int arg,char *s,char *type,char t[][16]);
  int isDeclaredfon(char *s);
  void Insertfonction(char *s,int arg,char *type,int proc);
  int Chercherfon(char *s);
  fonction *CHERCHEFON(char *s);
   int lineNumber,local;
   int firstloc=0,continst=0;
  char tokens[39][16] = {"debut","fin","Algorithme","retourne","si","alors","sinon","pour","faire","tantque","selonque","case","defaut","de","repeter","ftq","fpour","fsq","fsi","afficher","lire","par","jusqua","structure","Entier","Reel","Caractere","Chaine_Caractere","booleen","Fonction","Vrai","Faux","arret","continue","var","conste","Procedure"};
   char expr[300],exp1[300],instruc[200][300];
   char ex2[300];
   
   
   
   vars *base,*sommet,*first,*p;
   fonction *basefonction,*sommetfonction,*f;
   int conteurfonction,a=0;
   int conteur=0,conteurbase=0,c=0,c1=0;
   FILE *file;
   
   char k[10];

%}
%union {
char var1[255];
int entier;
float reel;
}

 
%type<var1> expr1 affectei expr term factor incdec appelfun bool comparexp termlogi condition declarationfun declarationfuns varreturn




%token ALGO DEBUT FIN // les lexemes que doit fournir yylex()
%token AFFECT DIFF SUP_E INF_E EGAL_EGAL ET OU A PTVIRG DEUX_POINT VIRG PLUS
%token MOIN MULT DIV NON MODULO PARENT_O PARENT_F CROCH_F CROCH_O AC_O AC_F
%token VAR RETOURNE SI ALORS SINON POUR FAIRE TANTQUE SELONQUE
%token REPETER FINTANTQUE FINPOUR FINSELONQUE FINSI AFFICHER LIRE 
%token PAR JUSQUA FONCTION VRAI FAUX CONTINUE ARRET DEFAUT
%token <entier>ENT <reel>REEL <var1>IDENTIF CH_CRT DE CAS  TYPE POINT POINT_EGAL CRT CONSTANTE
%token PLUS_PLUS MOIN_MOIN PLUS_EGAL MOIN_EGAL DIV_EGAL MULT_EGAL MODULO_EGAL VARIABLE
%token SUP INF PROCEDURE
%start program // l’axiome de notre grammaire
%%
program :ALGO IDENTIF {file=fopen(strcat($2,".c"),"w");fprintf(file,"#include<stdio.h>\n #include<string.h>\n");} declarations DEBUT{fprintf(file,"int main(){\n");}  listInstr FIN {affiche(continst,0);fprintf(file,"}");}
|ALGO IDENTIF DEBUT  listInstr FIN 
;
listInstr : listInstr inst
 | inst 
;

declarations: declarations declaration
        | declaration {if(firstloc==1){
                                        base=base->next;
                                        firstloc=0;
                                        }
                                        }
        | declarations function{dicoglobal();}
        | declarations procedure{dicoglobal();}
        | function{dicoglobal();}
        | procedure{dicoglobal();}
        ;
declaration: VARIABLE ensidentif DEUX_POINT TYPE PTVIRG{affect_type(0,$4);/*lparametre lawal dyal wax const ola la tadir 1 ila kan cnste*/
                                                        }                                             
            |CONSTANTE ensidentif DEUX_POINT TYPE PTVIRG{affect_type(1,$4);}
        ;
declarationfun: IDENTIF DEUX_POINT TYPE{affect_type_fun(0,$1,$3);
                                      strcpy(ex2,$3);
                                      returntype(ex2);
                                      sprintf($$,"%s %s",ex2,$1);
                                      }
        |IDENTIF CROCH_O ENT CROCH_F CROCH_O ENT CROCH_F DEUX_POINT TYPE {affect_type_fun(1,$1,$9);
                                                                          affect_indix($1,$3,$6);
                                                                          strcpy(ex2,$9);
                                                                          returntype(ex2);
                                                                          sprintf($$,"%s[%d][%d] %s",ex2,$3,$6,$1);
                                                                          }
        |IDENTIF  CROCH_O ENT CROCH_F DEUX_POINT TYPE {affect_type_fun(1,$1,$6);
                                                        affect_indix($1,$3,0);
                                                        strcpy(ex2,$6);
                                                        returntype(ex2);
                                                        sprintf($$,"%s[%d] %s",ex2,$3,$1);
                                                        }
;
declarationfuns:declarationfuns VIRG declarationfun {c++;sprintf(instruc[continst++],",%s",$3);}
     | declarationfun {if(firstloc==1){
                                      strcpy(instruc[continst++],$1);
                                      base=base->next;
                                      firstloc=0;}
                                      c++;}
;
ensidentif: ensidentif VIRG IDENTIF {identifTest(0,$3,tokens);
                                      p=CHERCHE($3);}
        | ensidentif VIRG IDENTIF CROCH_O ENT CROCH_F CROCH_O ENT CROCH_F {identifTest(1,$3,tokens);
                                            affect_indix($3,$5,$8);
                                            p=CHERCHE($3);/*lparametr lawal dyal wach tablo ola la tadir 1 ila kan tableu*/}
        | ensidentif VIRG IDENTIF CROCH_O ENT CROCH_F {identifTest(1,$3,tokens);
                                            affect_indix($3,$5,0);
                                            p=CHERCHE($3);/*lparametr lawal dyal wach tablo ola la tadir 1 ila kan tableu*/}
        |IDENTIF {identifTest(0,$1,tokens);
                  p=CHERCHE($1);}
        |IDENTIF CROCH_O ENT CROCH_F CROCH_O ENT CROCH_F {identifTest(1,$1,tokens);
                          affect_indix($1,$3,$6);
                          p=CHERCHE($1);}
        |IDENTIF  CROCH_O ENT CROCH_F {identifTest(1,$1,tokens);
                          affect_indix($1,$3,0);
                          p=CHERCHE($1);}
        ;
strccondition : SI  PARENT_O  condition PARENT_F ALORS listInstr FINSI
 | SI PARENT_O  condition PARENT_F ALORS listInstr SINON listInstr FINSI
;
condition: condition ET termlogi{sprintf(instruc[continst++],"%s && %s",$1,$3);}
  |condition OU termlogi {sprintf(instruc[continst++],"%s || %s",$1,$3);}
  | termlogi {sprintf(instruc[continst++],"%s ",$1);}
;

termlogi: PARENT_O condition PARENT_F{sprintf($$,"(%s)",$2);}
  | comparexp{sprintf($$,"%s",$1);}
;

comparexp: expr EGAL_EGAL expr{sprintf($$,"%s == %s",$1,$3);}
    |expr DIFF expr{sprintf($$,"%s != %s",$1,$3);}
    |expr SUP_E expr{sprintf($$,"%s >= %s",$1,$3);}
    |expr SUP expr{sprintf($$,"%s > %s",$1,$3);}
    |expr INF expr{sprintf($$,"%s <= %s",$1,$3);}
    |expr INF_E expr{sprintf($$,"%s < %s",$1,$3);}
   | expr EGAL_EGAL bool{sprintf($$,"%s == %s",$1,$3);}
   |expr DIFF bool{sprintf($$,"%s != %s",$1,$3);}
;


loop : POUR IDENTIF DE expr A expr FAIRE listInstr FINPOUR {isUsable($2);
                                                          p=CHERCHE($2);
                                                          if(strcmp(p->type,"Entier")!=0){printf("%s ",p->identif);
                                                                                         yyerror("doit étre de type entier");
                                                                                         }}
 | TANTQUE PARENT_O condition PARENT_F FAIRE listInstr FINTANTQUE
 |REPETER listInstr JUSQUA PARENT_O condition PARENT_F PTVIRG
;
listexpsais: listexpsais VIRG IDENTIF {isUsable($3);}
   | IDENTIF{isUsable($1);}
;
listexpaff: listexpaff VIRG expr1
   | listexpaff VIRG expr
   | expr1
   | expr
;
saisir : LIRE PARENT_O listexpsais PARENT_F 
;
ecrir  : AFFICHER PARENT_O listexpaff PARENT_F
;


swtch : SELONQUE PARENT_O expr PARENT_F FAIRE instselon DEFAUT DEUX_POINT listInstr FINSELONQUE
   | SELONQUE PARENT_O CRT PARENT_F FAIRE instselon DEFAUT DEUX_POINT listInstr FINSELONQUE
;
instselon : instselon cass
 | cass
;
cass : CAS expr DEUX_POINT listInstr ARRET PTVIRG | CAS expr1 DEUX_POINT listInstr ARRET PTVIRG
;
varreturn: expr{strcpy($$,$1);}
  | bool{strcpy($$,$1);}
;
function:  FONCTION IDENTIF PARENT_O declarationfuns PARENT_F DEUX_POINT TYPE declarations DEBUT listInstr RETOURNE varreturn FIN {fonctionTest(0,c,$2,$7,tokens);
                                                                                                                                      strcpy(exp1,$12);
                                                                                                                                      if((strcmp(sommetfonction->type,"Reel")==0)||(strcmp(sommetfonction->type,"Entier")==0)||(strcmp(sommetfonction->type,"booleen")==0)){
                                                                                                                                        
                                                                                                                                        }else{
                                                                                                                                          yyerror("ce type est interdit pour les fonctions  ");
                                                                                                                                          }
                                                                                                                                      if(strcmp(sommetfonction->type,"booleen")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$12);
                                                                                                                                        strcat(exp1,"%2");
                                                                                                                                        }
                                                                                                                                        if(strcmp(sommetfonction->type,"Entier")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$12);
                                                                                                                                        
                                                                                                                                        }
                                                                                                                                        
                                                                                                                                        strcpy(ex2,$7);
                                                                                                                                        returntype(ex2);
                                                                                                                                        
                                                                                                                                        fprintf(file,"%s %s(",ex2,$2);
                                                                                                                                        affiche(c,0);
                                                                                                                                        fprintf(file,"){\n");
                                                                                                                                        affiche(continst,c);
                                                                                                                                        continst=0;
                                                                                                                                        fprintf(file,"return %s;\n }\n",exp1);
                                                                                                                                        c=0;
                                                                                                                                        }
   | FONCTION IDENTIF PARENT_O declarationfuns PARENT_F DEUX_POINT TYPE DEBUT listInstr RETOURNE varreturn FIN{fonctionTest(0,c,$2,$7,tokens);
                                                                                                                                      strcpy(exp1,$11);
                                                                                                                                      if((strcmp(sommetfonction->type,"Reel")==0)||(strcmp(sommetfonction->type,"Entier")==0)||(strcmp(sommetfonction->type,"booleen")==0)){
                                                                                                                                        
                                                                                                                                        }else{
                                                                                                                                          yyerror("ce type est interdit pour les fonctions  ");
                                                                                                                                          }
                                                                                                                                      if(strcmp(sommetfonction->type,"booleen")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$11);
                                                                                                                                        strcat(exp1,"%2");
                                                                                                                                        }
                                                                                                                                        if(strcmp(sommetfonction->type,"Entier")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$11);
                                                                                                                                        
                                                                                                                                        }
                                                                                                                                        
                                                                                                                                        strcpy(ex2,$7);
                                                                                                                                        returntype(ex2);
                                                                                                                                        
                                                                                                                                        fprintf(file,"%s %s(",ex2,$2);
                                                                                                                                        affiche(c,0);
                                                                                                                                        fprintf(file,"){\n");
                                                                                                                                        affiche(continst,c);
                                                                                                                                        continst=0;
                                                                                                                                        fprintf(file,"return %s;\n }\n",exp1);
                                                                                                                                        c=0;
                                                                                                                      }
   | FONCTION IDENTIF PARENT_O PARENT_F DEUX_POINT TYPE declarations DEBUT listInstr RETOURNE varreturn FIN{fonctionTest(0,0,$2,$6,tokens);
                                                                                                            strcpy(exp1,$11);
                                                                                                                                      if((strcmp(sommetfonction->type,"Reel")==0)||(strcmp(sommetfonction->type,"Entier")==0)||(strcmp(sommetfonction->type,"booleen")==0)){
                                                                                                                                        
                                                                                                                                        }else{
                                                                                                                                          yyerror("ce type est interdit pour les fonctions  ");
                                                                                                                                          }
                                                                                                                                      if(strcmp(sommetfonction->type,"booleen")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$11);
                                                                                                                                        strcat(exp1,"%2");
                                                                                                                                        }
                                                                                                                                        if(strcmp(sommetfonction->type,"Entier")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$11);
                                                                                                                                        
                                                                                                                                        }
                                                                                                                                        
                                                                                                                                        strcpy(ex2,$6);
                                                                                                                                        returntype(ex2);
                                                                                                                                        
                                                                                                                                        fprintf(file,"%s %s(",ex2,$2);
                                                                                                                                        
                                                                                                                                        fprintf(file,"){\n");
                                                                                                                                        affiche(continst,c);
                                                                                                                                        continst=0;
                                                                                                                                        fprintf(file,"return %s;\n }\n",exp1);
                                                                                                                                        
                                                                                                                  }
   | FONCTION IDENTIF PARENT_O PARENT_F DEUX_POINT TYPE DEBUT listInstr RETOURNE varreturn FIN{fonctionTest(0,0,$2,$6,tokens);
                                                                                                  strcpy(exp1,$10);
                                                                                                                                      if((strcmp(sommetfonction->type,"Reel")==0)||(strcmp(sommetfonction->type,"Entier")==0)||(strcmp(sommetfonction->type,"booleen")==0)){
                                                                                                                                        
                                                                                                                                        }else{
                                                                                                                                          yyerror("ce type est interdit pour les fonctions  ");
                                                                                                                                          }
                                                                                                                                      if(strcmp(sommetfonction->type,"booleen")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$10);
                                                                                                                                        strcat(exp1,"%2");
                                                                                                                                        }
                                                                                                                                        if(strcmp(sommetfonction->type,"Entier")==0){
                                                                                                                                        strcpy(exp1,"(int)");
                                                                                                                                        strcat(exp1,$10);
                                                                                                                                        
                                                                                                                                        }
                                                                                                                                        
                                                                                                                                        strcpy(ex2,$6);
                                                                                                                                        returntype(ex2);
                                                                                                                                        
                                                                                                                                        fprintf(file,"%s %s(",ex2,$2);
                                                                                                                                        
                                                                                                                                        fprintf(file,"){\n");
                                                                                                                                        affiche(continst,c);
                                                                                                                                        continst=0;
                                                                                                                                        fprintf(file,"return %s;\n }\n",exp1);
                                                                                                                                        }
   
;
procedure:  PROCEDURE IDENTIF PARENT_O declarationfuns PARENT_F DEBUT listInstr FIN{fonctionTest(1,c,$2,"NULL",tokens);
                                                                                                                                                                      
                                                                                    fprintf(file,"void %s(",$2);
                                                                                    affiche(c,0);
                                                                                    fprintf(file,"){\n");
                                                                                    affiche(continst,c);
                                                                                    continst=0;
                                                                                    fprintf(file," }\n");
                                                                                    c=0;}
   | PROCEDURE IDENTIF PARENT_O declarationfuns PARENT_F declarations DEBUT listInstr FIN {fonctionTest(1,c,$2,"NULL",tokens);
                                                                                                fprintf(file,"void %s(",$2);
                                                                                    affiche(c,0);
                                                                                    fprintf(file,"){\n");
                                                                                    affiche(continst,c);
                                                                                    continst=0;
                                                                                    fprintf(file," }\n");
                                                                                    c=0;
                                                                                                }
   | PROCEDURE IDENTIF PARENT_O PARENT_F DEBUT listInstr FIN {fonctionTest(1,0,$2,"NULL",tokens);
                                                                fprintf(file,"void %s(",$2);
                                                                                    
                                                                                    fprintf(file,"){\n");
                                                                                    affiche(continst,c);
                                                                                    continst=0;
                                                                                    fprintf(file," }\n");
                                                                                    }
   | PROCEDURE IDENTIF PARENT_O PARENT_F declarations DEBUT listInstr FIN{fonctionTest(1,0,$2,"NULL",tokens);
                                                                            fprintf(file,"void %s(",$2);
                                                                                    
                                                                                    fprintf(file,"){\n");
                                                                                    affiche(continst,c);
                                                                                    continst=0;
                                                                                    fprintf(file," }\n");
                                                                                    }
;

appelvars: appelvars VIRG expr{c1++;}
   | expr{c1++;}
   ;

appelfun: IDENTIF PARENT_O appelvars PARENT_F {f=CHERCHEFON($1);
                                              if(f==NULL){
                                                yyerror("fonction inconnu");}
                                                if(f->proc==1){
                                                  yyerror("les procedures ne retournent aucune valeur");}
                                                  if(f->arg!=c1){
                                                    yyerror("trop peu d'arguments pour fonctionner");}
                                                    sprintf($$,"%f",f->valretour);c1=0;}
    | IDENTIF PARENT_O PARENT_F {f=CHERCHEFON($1);
                                  if(f==NULL){
                                    yyerror("fonction inconnu");}
                                  if(f->proc==1){
                                    yyerror("les procedures ne retournent aucune valeur");}
                                    if(f->arg!=c1){
                                      yyerror("trop peu d'arguments pour fonctionner");}
                                       sprintf($$,"%f",f->valretour);;c1=0;}
;
appelproc: IDENTIF PARENT_O appelvars PARENT_F PTVIRG {f=CHERCHEFON($1);
                                                        if(f==NULL){
                                                          yyerror("fonction inconnu");}
                                                          c1=0;}
    | IDENTIF PARENT_O PARENT_F PTVIRG {f=CHERCHEFON($1);
                                        if(f==NULL){
                                          yyerror("fonction inconnu");}
                                          if(f->arg!=c1){
                                            yyerror("trop peu d'arguments pour fonctionner");}
                                          c1=0;};

affectei:IDENTIF CROCH_O ENT CROCH_F CROCH_O ENT CROCH_F{isUsable($1);
                        p=CHERCHE($1);
                        strcpy(ex2,p->identif);
                        if(p->lignex<=$3 || p->colonney<=$6 ||$3<0||$6<0){
                          yyerror("erreur segmentation");
                        }
                        sprintf($$,"%s[%d][%d]",$1,$3,$6);
        }

        |IDENTIF CROCH_O ENT CROCH_F{isUsable($1);
                        p=CHERCHE($1);
                        strcpy(ex2,p->identif);
                        
                        if(p->lignex<=$3||$3<0){
                          yyerror("erreur segmentation");
                        }
                        sprintf($$,"%s[%d]",$1,$3);
        }
        ;
inst : affectei AFFECT expr PTVIRG {
                                    p=CHERCHE(ex2);
                                  if((strcmp(p->type,"Caractere")==0)||(strcmp(p->type,"Chaine_Caractere")==0)){
                                    yyerror("les  types ne sont pas compatibles  ");}
                                  if(p->cnst==1&&p->checkval==1){
                                    printf("%s ",p->identif);yyerror("est constante");}
                                    if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est tableau d'entier");
                                            }
                                      }
                                        
                                         sprintf(instruc[continst++],"%s = %s;\n",$1,$3);
                                        p->checkval=1;
                                        
                                        }
 |IDENTIF AFFECT expr1 PTVIRG {isUsable($1);
                               p=CHERCHE($1);
                               if(p->cnst==1&&p->checkval==1){
                                 printf("%s ",p->identif);yyerror("est constante");}
                                 if((strcmp(p->type,"Entier")==0)||(strcmp(p->type,"Reel")==0)){
                                   yyerror("les  types ne sont pas compatibles  ");}
                                   if((strcmp(p->type,"Caractere")==0)&&strlen($3)>3){
                                     yyerror("la variable est type caractere");}
                                     strcpy(p->val,$3);
                                     p->checkval=1;}
 |affectei PLUS_EGAL expr PTVIRG {
                                p=CHERCHE(ex2);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);
                                  yyerror("est constante");}
                                  if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est tableau d'entier");
                                            }
                                      }
                                        
                                         sprintf(instruc[continst++],"%s += %s;\n",$1,$3);
                                 }
 |affectei MOIN_EGAL expr PTVIRG {
                                p=CHERCHE(ex2);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);
                                  yyerror("est constante");}
                                  if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est tableau d'entier");
                                            }
                                      }
                                        
                                         sprintf(instruc[continst++],"%s -= %s;\n",$1,$3);}
 |affectei DIV_EGAL expr PTVIRG {
                                p=CHERCHE(ex2);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);yyerror("est constante");}
                                if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est tableau d'entier");
                                            }
                                      }
                                        
                                         sprintf(instruc[continst++],"%s /= %s;\n",$1,$3);}
 |affectei MULT_EGAL expr PTVIRG {
                                p=CHERCHE("ex2");
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);
                                  yyerror("est constante");}
                                  if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est tableau d'entier");
                                            }
                                      }
                                        
                                         sprintf(instruc[continst++],"%s *= %s;\n",$1,$3);}
 |affectei MODULO_EGAL expr PTVIRG {
                                    p=CHERCHE(ex2);
                                    if(p->cnst==1&&p->checkval==1){
                                      printf("%s ",p->identif);yyerror("est constante");}
                                      if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est tableau d'entier");
                                            }
                                            sprintf(expr,"%d",(int)atof($3));
                                            sprintf(instruc[continst++],"%s%=%s\n",$1,expr);
                                      }else{
                                            printf("%s ",$1);yyerror("n'est pas entier");
                                      }
                                        
                                         }
  | IDENTIF AFFECT expr PTVIRG {isUsable($1);{}
                                    p=CHERCHE($1);
                                  if((strcmp(p->type,"Caractere")==0)||(strcmp(p->type,"Chaine_Caractere")==0)){
                                    yyerror("les  types ne sont pas compatibles  ");}
                                  if(p->cnst==1&&p->checkval==1){
                                    printf("%s ",p->identif);yyerror("est constante");}
                                    if(strcmp(p->type,"Entier")==0){
                                      sprintf($1,"%d",(int)atof($3));}
                                      else{
                                        strcpy($1,$3);}
                                        p->checkval=1;
                                        if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est un entier");
                                            }
                                      }
                                        
                                         sprintf(instruc[continst++],"%s=%s;\n",p->identif,$3);
                                        }

 |IDENTIF PLUS_EGAL expr PTVIRG {isUsable($1);
                                p=CHERCHE($1);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);
                                  yyerror("est constante");}
                                  if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est un entier");
                                            }
                                      }
                                      if(p->checkval==0){printf("%s ",p->identif);yyerror("n'a pas un valeur initial");}
                                         sprintf(instruc[continst++],"%s += %s;\n",$1,$3);}
 |IDENTIF MOIN_EGAL expr PTVIRG {isUsable($1);
                                p=CHERCHE($1);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);
                                  yyerror("est constante");}
                                  if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est un entier");
                                            }
                                      }
                                        if(p->checkval==0){printf("%s ",p->identif);yyerror("n'a pas un valeur initial");}
                                         sprintf(instruc[continst++],"%s -= %s;\n",$1,$3);}
 |IDENTIF DIV_EGAL expr PTVIRG {isUsable($1);
                                p=CHERCHE($1);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);yyerror("est constante");}
                                if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est un entier");
                                            }
                                      }
                                        if(p->checkval==0){printf("%s ",p->identif);yyerror("n'a pas un valeur initial");}
                                         sprintf(instruc[continst++],"%s /=%s;\n",$1,$3);}
 |IDENTIF MULT_EGAL expr PTVIRG {isUsable($1);
                                p=CHERCHE($1);
                                if(p->cnst==1&&p->checkval==1){
                                  printf("%s ",p->identif);
                                  yyerror("est constante");}
                                 if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",p->identif);yyerror("est un entier");
                                            }
                                      }
                                        if(p->checkval==0){printf("%s ",p->identif);yyerror("n'a pas un valeur initial");}
                                         sprintf(instruc[continst++],"%s *=%s;\n",$1,$3);}
 |IDENTIF MODULO_EGAL expr PTVIRG {isUsable($1);
                                    p=CHERCHE($1);
                                    if(p->cnst==1&&p->checkval==1){
                                      printf("%s ",p->identif);yyerror("est constante");}
                                      if(strcmp(p->type,"Entier")==0 ){
                                           if((int)atof($3)!=atof($3)){
                                                printf("%s ",$3);yyerror("n'est pas entier");
                                            }
                                            sprintf(expr,"%d",(int)atof($3));
                                            sprintf(instruc[continst++],"%s %= %s;\n",$1,expr);
                                      }else{
                                            printf("%s ",p->identif);yyerror("n'est pas entier");
                                      }
                                      if(p->checkval==0){printf("%s ",p->identif);yyerror("n'a pas un valeur initial");}}
 |swtch 
 |loop 
 |strccondition 
 |saisir PTVIRG 
 |ecrir  PTVIRG 
 |ARRET PTVIRG
 |CONTINUE PTVIRG
 |IDENTIF AFFECT PARENT_O condition PARENT_F PTVIRG  {sprintf(instruc[continst++],"%s = (%s);\n",$1,$4);}
 |appelproc 
  |incdec PTVIRG{sprintf(instruc[continst++],"%s ;\n",$1);}
;
expr    : expr PLUS term {sprintf($$,"%s + %s",$1,$3);}
        | expr MOIN term {sprintf($$,"%s - %s",$1,$3);}
        | term{sprintf($$,"%s",$1);}
        ;

term    : term MULT factor {sprintf($$,"%s * %s",$1,$3);}
        | term DIV factor  {sprintf($$,"%s / %s",$1,$3);}
        | term MODULO factor {sprintf($$,"%s /% %s",$1,$3);}
        | factor{sprintf($$,"%s",$1);}
        ;

factor  : ENT  {sprintf($$,"%d",$1);}
        | REEL{sprintf($$,"%f",$1);}
        | IDENTIF {isUsable($1);
                        p=CHERCHE($1);
                        if(p->checkval==0){
                          printf("%s :: ",p->identif);yyerror("en utilise variable null");
                          }
                        strcpy($$,p->identif);
                        if(p->tab==1){
                           yyerror("vous ne pouvez pas affecter un tableau a un variable");
                        }
                        sprintf($$,"%s",p->identif);
                  }
        | IDENTIF CROCH_O ENT CROCH_F{isUsable($1);
                        p=CHERCHE($1);
                        if(p->checkval==0){
                          yyerror("en utilise variable null");
                          }
                        sprintf($$,"%s[%d]",$1,$3);
                        if(p->lignex<=$3){
                          yyerror("erreur segmentation");
                        }
                        sprintf($$,"%s[%d]",p->identif,$3);

        }
        | IDENTIF CROCH_O ENT CROCH_F CROCH_O ENT CROCH_F{isUsable($1);
                        p=CHERCHE($1);
                        if(p->checkval==0){
                          yyerror("en utilise variable null");
                          }
                       
                        if(p->lignex<=$3 || p->colonney<=$6 ){
                          yyerror("erreur segmentation");
                        }

                       sprintf($$,"%s[%d][%d]",$1,$3,$6);

        }
        | appelfun{sprintf($$,"%s",$1);}
        | incdec{sprintf($$,"%s",$1);}
        
        |MOIN factor {sprintf($$,"- %s",$2);}
        | PARENT_O expr PARENT_F{strcpy(expr,"(");
                                strcat(expr,$2);
                                strcat(expr,")");
                                strcpy($$,expr);
                                }
                            
        ;
incdec:PLUS_PLUS IDENTIF{isUsable($2);
                          p=CHERCHE($2);
                          if(p->cnst==1&&p->checkval==1){
                            printf("%s ",p->identif);yyerror("est constante");}
                            if(p->checkval==0){
                              yyerror("la variable est null");}
                              sprintf($$,"++%s",p->identif);
                              }
        | MOIN_MOIN IDENTIF{isUsable($2);
                            p=CHERCHE($2);
                            if(p->cnst==1&&p->checkval==1){
                              printf("%s ",p->identif);yyerror("est constante");}
                              if(p->checkval==0){
                                yyerror("la variable est null");}
                                sprintf($$,"--%s",p->identif);}
        | IDENTIF PLUS_PLUS{isUsable($1);
                            p=CHERCHE($1);
                            if(p->cnst==1&&p->checkval==1){
                              printf("%s ",p->identif);
                              yyerror("est constante");}
                              if(p->checkval==0){
                                yyerror("la variable est null");}
                                sprintf($$,"%s++",p->identif);}
        | IDENTIF MOIN_MOIN{isUsable($1);
                            p=CHERCHE($1);
                            if(p->cnst==1&&p->checkval==1){
                              printf("%s ",p->identif);
                              yyerror("est constante");}
                              if(p->checkval==0){
                                yyerror("la variable est null");}
                                sprintf($$,"%s--",p->identif);}
expr1: CH_CRT{strcpy($$,$1);}
  | CRT{strcpy($$,$1);}
;
bool: VRAI{sprintf($$,"1");}
  | FAUX{sprintf($$,"0");}
;
%%
void returntype(char *s){
  if(strcmp(s,"Entier")==0||strcmp(s,"booleen")==0){
          strcpy(s,"int");
        }
  if(strcmp(s,"Reel")==0){
          strcpy(s,"float");
        }
  if(strcmp(s,"Caractere")==0){
          strcpy(s,"char");
        }
        
}
/**************************************************** FONCTION ET PROCEDURE*****************************************************************/
fonction *Creationfon(char *s){
  fonction *p;
  p=(fonction *)malloc(sizeof(fonction));
  
  strcpy(p->name,s);

  p->next=NULL;
  return p;
}
void fonctionTest(int proc,int arg,char *s,char *type,char t[][16]){
  if (isToken(s,t) == -1){
    yyerror("Declaration d'une vfonction avec un nom de token\n");
  }
  if (isDeclaredfon(s) == -1){
    yyerror("Declaration de deux fonction avec le meme nom\n");
    
  }
  
  Insertfonction(s,arg,type,proc);

}
////////////////////////////////////////////////////////////////////
void Insertfonction(char *s,int arg,char *type,int proc){
  fonction *new;
  if(conteurfonction==0){
      basefonction=Creationfon(s);
      
      sommetfonction=basefonction;
      
  } else {
      new=Creationfon(s);
      
      sommetfonction->next=new;
      
      sommetfonction =sommetfonction->next;
  }
  sommetfonction->arg=arg;
  sommetfonction->conteur=conteurfonction;
  conteurfonction++;
  strcpy(sommetfonction->type,type);
  sommetfonction->proc=proc;
  
  
}
////////////////////////////////////////////////////////////////:
int isDeclaredfon(char *s){
  if (Chercherfon(s) == 0)
      return -1;
  return 0;
}
///////////////////////////////////////////////////////////////////
int Chercherfon(char *s){
     int l=1;fonction *p;
     p=basefonction;
     while(p!=NULL){
      if(strcmp(s,p->name)==0){
        l=0;
        break;
      }
      p=p->next;
     }

     return l;
}
//////////////////////////////////////////////////////////////:
fonction *CHERCHEFON(char *s){
    int l=1;fonction *p;
     p=basefonction;
     while(p!=NULL){
      if(strcmp(s,p->name)==0){
        l=0;
        break;
      }
      p=p->next;
     }
     
     return p;
}
/**************************************************** VARIABLE*****************************************************************/
///////////////////////////////////////////////////////////////////////
void dicolocal(){
  
  if(local==0){
  base=sommet;
  conteurbase=conteur;
  local=1;}
  
}
///////////////////////////////////////////////////////////////////////
void dicoglobal(){
  
  vars *p,*q;
  int i=0;  
  
  sommet=first;
  do{
    sommet=sommet->next;
    
  }while(sommet->conteur<base->conteur-1);
  p=sommet->next;
  while(p!=NULL){
    q=p->next;
    
    free(p);
    p=q;
  }
  base=first;
  conteur=conteurbase;
  
}
///////////////////////////////////////////////////////////////////////
vars *Creation(char *s){
  vars *p;
  p=(vars *)malloc(sizeof(vars));
  
  strcpy(p->identif,s);
  p->checkval=0;
  p->lignex=0;
  p->colonney=0;
  p->next=NULL;
  return p;
}
///////////////////////////////////////////////////////////////////////
void Insertvar(char *s,int tab){
  vars *new;
  if(conteur==0){
      first=Creation(s);
      base=first;
      sommet=base;
      
  } else {
      new=Creation(s);
      
      sommet->next=new;
      
      sommet =sommet->next;
  }
  
  sommet->conteur=conteur;
  conteur++;
  sommet->ligne=lineNumber;
  sommet->tab=tab;
  
}
///////////////////////////////////////////////////////////////////////
void affect_indix(char *s,int a,int b){
  vars *p;
  p=CHERCHE(s);
  p->lignex=a;
  p->colonney=b;   
     
}
///////////////////////////////////////////////////////////////////////
vars *CHERCHE(char *s){
    int l=1;vars *p;
     p=base;
     while(p!=NULL){
      if(strcmp(s,p->identif)==0){
        l=0;
        break;
      }
      p=p->next;
     }
     if(l==1){
       p=first;
       while(p->conteur<base->conteur-1){
          if(strcmp(s,p->identif)==0){
            l=0;
            break;
           }
           p=p->next;
       }
     }
     return p;
}
///////////////////////////////////////////////////////////////////////
int Chercher(char *s){
     int l=1,i=0;vars *p;
     p=base;
     while(p!=NULL){
      if(strcmp(s,p->identif)==0){
        l=0;
        break;
      }
      p=p->next;
     }

     return l;
}

///////////////////////////////////////////////////////////////////////
void afficher(){
  /*fonction *p;
  p=basefonction;
  int i=0;

  while(i++<conteurbase){
    printf("\n %-15s   %-15s  %-15d  \t",p->name,p->type,p->arg);
    
    if(p->proc==1)printf("procedure \t");
    else printf("fonction \t");
    
      
        
      
    printf("\n");
    p=p->next;
  }
  
 vars *p;
  p=base;
  int i=0;

  while(i++<conteur){
    printf("\n %s   %s  %d\t",p->identif,p->type,p->ligne);
    
    if(p->cnst==1)printf("constante \t");
    else printf("variable \t");
    if(p->tab==1){
      printf("tableau \t");
       printf(" %d    %d",p->lignex,p->colonney);
      }
      
       
      
    printf("\n");
    p=p->next;
  
  
}*/
 
}
///////////////////////////////////////////////////////////////////////
void affect_type_fun(int tab,char s[31],char type[20]){
  identifTest(tab,s,tokens);
  strcpy(sommet->type,type);
  
}
///////////////////////////////////////////////////////////////////////
void affect_type(int a,char s[20]){
     vars *p;
     p=base;
     while(p!=NULL && p->ligne<=lineNumber){
      if(p->ligne==lineNumber){
        strcpy(p->type,s);
        p->cnst=a;
        char d[20];
        strcpy(d,s);
          returntype(d);
          if(p->lignex==0 && p->colonney==0)sprintf(instruc[continst++],"%s %s ;\n",d,p->identif);
          if(p->lignex!=0 && p->colonney==0)sprintf(instruc[continst++],"%s %s[%d] ;\n",d,p->identif,p->lignex);
          if(p->lignex!=0 && p->colonney!=0)sprintf(instruc[continst++],"%s %s[%d][%d] ;\n",d,p->identif,p->lignex,p->colonney);
        
        
      }
      p=p->next;
     }
}
///////////////////////////////////////////////////////////////////////
int isToken(char *s,char t[][16]){
  int i;
  for(i=0;i<38;i++)
    if (strcmp(s,t[i]) == 0)
      return -1;
  return 0;
}
///////////////////////////////////////////////////////////////////////
int isDeclared(char *s){
  if (Chercher(s) == 0)
      return -1;
  return 0;
}
///////////////////////////////////////////////////////////////////////
int cherche(char *s){  
     int l=1;vars *p;
     p=base;
     while(p!=NULL){
      if(strcmp(s,p->identif)==0){
        l=0;
        break;
      }
      p=p->next;
     }
     if(l==1){
       p=first;
       while(p->conteur<base->conteur){
          if(strcmp(s,p->identif)==0){
            l=0;
            break;
           }
           p=p->next;
       }
     }
     return l;
}
///////////////////////////////////////////////////////////////////////
int isDeclared2(char *s){
    if(cherche(s)==0)
       return -1;
    return 0;
}
///////////////////////////////////////////////////////////////////////
void isUsable(char *s){
    if (isDeclared2(s) == 0){
      yyerror("Vous avez utilisée une variable non déclarée\n");
      
    }
}
///////////////////////////////////////////////////////////////////////
void identifTest(int tab,char *s,char t[][16]){
  if (isToken(s,t) == -1){
    yyerror("Déclaration d'une variable avec un nom de token\n");
    
  }
  if (isDeclared(s) == -1){
    yyerror("Declaration de deux variables avec le meme nom\n");
    
  }
  Insertvar(s,tab);
}
//////////////////////////////////////////////////////////////////////////

void yyerror( const char * msg){
    printf("line %d : %s", lineNumber, msg);
    exit(-1);
}
void affiche(int a,int b){
  int i;
  for(i=b;i<a;i++){
        fprintf(file,"%s",instruc[i]);
  }
  
}
int main(int argc,char ** argv){
    if(argc>1) yyin=fopen(argv[1],"r"); // check result !!!
    lineNumber=1;
    int i;
    if(!yyparse()){
      
      
      fclose(file);
      printf("Expression correct\n");
    }
      
  return(0);
}
