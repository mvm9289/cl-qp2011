/* ===== semantic.c ===== */
#include <string>
#include <iostream>
#include <map>
#include <list>
#include <vector>

using namespace std;

#include <stdio.h>
#include <stdlib.h>

#include "ptype.hh"
#include "symtab.hh"
#include "codegest.hh"

#include "myASTnode.hh"

#include "util.hh"
#include "semantic.hh"

#include "codegen.hh"

//#define __DEBUG__ 0

// symbol table with information about identifiers in the program
// declared in symtab.cc
extern symtab symboltable;

// When dealing with a list of instructions, it contains the maximum auxiliar space
// needed by any of the instructions for keeping non-referenceable non-basic-type values.
int maxoffsetauxspace;

// When dealing with one instruction, it contains the auxiliar space
// needed for keeping non-referenceable values.
int offsetauxspace;

// For distinghishing different labels for different if's and while's.
int newLabelWhile(bool inicialitzar = false){
  static int comptador = 1;
  if (inicialitzar) comptador = 0;
  return comptador++;
}

int newLabelIf(bool inicialitzar = false){
  static int comptador = 1;
  if (inicialitzar) comptador = 0;
  return comptador++;
}


codechain indirections(int jumped_scopes,int t)
{
  codechain c;
  if (jumped_scopes==0) {
    c="aload static_link t"+itostring(t);
  }
  else {
    c="load static_link t"+itostring(t);
    for (int i=1;i<jumped_scopes;i++) {
      c=c||"load t"+itostring(t)+" t"+itostring(t);
    }
  }
  return c;
}

int compute_size(ptype tp)
{
  if (isbasickind(tp->kind)) {
    tp->size=4;
  }
  else if (tp->kind=="array") {
    tp->size=tp->numelemsarray*compute_size(tp->down);
  }
  else if (tp->kind=="struct") {
    tp->size=0;
    for (list<string>::iterator it=tp->ids.begin();it!=tp->ids.end();it++) {
      tp->offset[*it]=tp->size;
      tp->size+=compute_size(tp->struct_field[*it]);
    }
  }
  return tp->size;
}

void gencodevariablesandsetsizes(scope *sc,codesubroutine &cs,bool isfunction=0)
{
  if (isfunction) cs.parameters.push_back("returnvalue");
  for (list<string>::iterator it=sc->ids.begin();it!=sc->ids.end();it++) {
    if (sc->m[*it].kind=="idvarlocal") {
      variable_data vd;
      vd.name="_"+(*it);
      vd.size=compute_size(sc->m[*it].tp);
      cs.localvariables.push_back(vd);
    } else if (sc->m[*it].kind=="idparval" || sc->m[*it].kind=="idparref") {
      compute_size(sc->m[*it].tp);
      cs.parameters.push_back("_"+(*it));
    } else if (sc->m[*it].kind=="idfunc") {
      // Here it is assumed that in tp->right is kept the return value type
      // for the case of functions. If this is not the case you must
      // change this line conveniently in order to force the computation
      // of the size of the type returned by the function.
      compute_size(sc->m[*it].tp->right);
    } else if (sc->m[*it].kind=="idproc") {
      // Nothing to be done.
    }
  }
  cs.parameters.push_back("static_link");
}

codechain GenLeft(AST *a,int t);
codechain GenRight(AST *a,int t);

void CodeGenRealParams(AST *a,ptype tp,codechain &cpushparam,codechain &cremoveparam,int t)
{
  if (!a) return;
  
  #ifdef __DEBUG__
  cout<<"[CodeGenRealParams]: Starting with node \""<<a->kind<<"\""<<endl;
  #endif

  for (AST *a1=a; a1!=0; a1=a1->right)
  {
    if (tp->kind == "parval")
    {
      if (isbasickind(tp->down->kind))
        cpushparam=cpushparam||GenRight(a1, t);
      else if (tp->down->kind=="array")
      {
        cpushparam=cpushparam||
          GenLeft(a1,t+1)||
          "aload aux_space t"+itostring(t)||
          "addi t"+itostring(t)+" "+itostring(offsetauxspace)+" t"+itostring(t)||
          "copy t"+itostring(t+1)+" t"+itostring(t)+" "+itostring(tp->down->size*tp->down->numelemsarray);
        offsetauxspace+=tp->down->size*tp->down->numelemsarray;
        if (offsetauxspace > maxoffsetauxspace) maxoffsetauxspace = offsetauxspace;
      }
    }
    else // tp-kind == "parref"
      cpushparam=cpushparam||GenLeft(a1, t);
    cpushparam=cpushparam||"pushparam t"+itostring(t);
    cremoveparam=cremoveparam||"killparam";
    tp = tp->right;
  }
  
  #ifdef __DEBUG__
  cout<<"[CodeGenRealParams]: Ending with node \""<<a->kind<<"\""<<endl;
  #endif
}

// ...to be completed:
codechain GenLeft(AST *a,int t)
{
  codechain c;

  if (!a) return c;

  #ifdef __DEBUG__
  cout<<"[GenLeft]: Starting with node \""<<a->kind<<"\""<<endl;
  #endif
  
  if (a->kind=="ident")
  {
    if (symboltable.jumped_scopes(a->text)==0 && symboltable[a->text].kind != "idparref" &&
        (symboltable[a->text].kind != "idparval" || isbasickind(a->tp->kind)))
      c="aload _"+a->text+" t"+itostring(t);
    else if (symboltable.jumped_scopes(a->text)==0 && ((symboltable[a->text].kind == "idparval" &&
        !isbasickind(a->tp->kind)) || symboltable[a->text].kind == "idparref"))
      c="load _"+a->text+" t"+itostring(t);
    else //if (symboltable.jumped_scopes(a->text) > 0)
    {
      c=indirections(symboltable.jumped_scopes(a->text),t)||
        "addi t"+itostring(t)+" offset("+symboltable.idtable(a->text)+":_"+a->text+") t"+itostring(t);
    }
    //else c="load _"+a->text+" t"+itostring(t);
  }
  else if (a->kind==".")
  {
    c=GenLeft(child(a,0),t)||
      "addi t"+itostring(t)+" "+
      itostring(child(a,0)->tp->offset[child(a,1)->text])+" t"+itostring(t);
  }
  else if (a->kind=="[")
  {
    c=GenLeft(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "muli t"+itostring(t+1)+" "+itostring(a->tp->size)+" t"+itostring(t+1);
    c=c||"addi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else
  {
    cout<<"BIG PROBLEM! No case defined for kind "<<a->kind<<endl;
  }
  
  #ifdef __DEBUG__
  cout<<"[GenLeft]: Ending with node \""<<a->kind<<"\""<<endl;
  #endif
  
  return c;
}


// ...to be completed:
codechain GenRight(AST *a,int t)
{
  codechain c;

  if (!a) return c;

  #ifdef __DEBUG__
  cout<<"[GenRight]: Starting with node \""<<a->kind<<"\""<<endl;
  #endif
  
  if (a->ref)
  {
    if (a->kind=="ident" && symboltable.jumped_scopes(a->text)==0 &&
      isbasickind(symboltable[a->text].tp->kind) && symboltable[a->text].kind!="idparref")
    {
      c="load _"+a->text+" t"+itostring(t);
    }
    else if (isbasickind(a->tp->kind))
    {
      c=GenLeft(a,t)||"load t"+itostring(t)+" t"+itostring(t);
      if (symboltable.jumped_scopes(a->text)>0 && symboltable[a->text].kind=="idparref")
        c=c||"load t"+itostring(t)+" t"+itostring(t);
    }
    else
    {
      // To be done.
    }    
  } 
  else if (a->kind=="intconst")
  {
    c="iload "+a->text+" t"+itostring(t);
  }
  else if (a->kind=="+")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "addi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind=="-")
  {
    if (!child(a, 1))
    {
      c=GenRight(child(a,0), t)||
        "mini t"+itostring(t)+" t"+itostring(t);
    }
    else
    {
      c=GenRight(child(a,0),t)||
        GenRight(child(a,1),t+1)||
        "subi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
    }
  }
  else if (a->kind=="*")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "muli t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind=="/")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "divi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind == "<")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "lesi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind == ">")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "grti t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind == "=")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "equi t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind == "and")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "land t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind == "or")
  {
    c=GenRight(child(a,0),t)||
      GenRight(child(a,1),t+1)||
      "loor t"+itostring(t)+" t"+itostring(t+1)+" t"+itostring(t);
  }
  else if (a->kind == "not")
  {
    c=GenRight(child(a,0),t)||
      "lnot t"+itostring(t)+" t"+itostring(t);
  }
  else if (a->kind == "true" || a->kind == "false")
  {
    c="iload "+itostring(a->kind=="true")+" t"+itostring(t);
  }
  else if (a->kind == "(")
  {
    codechain cpushparam;
    if (isbasickind(child(a,0)->tp->right->kind))
      cpushparam = "pushparam 0";
    else if (child(a,0)->tp->right->kind=="array")
    {
      cpushparam = "aload aux_space t"+itostring(t)||
        "addi t"+itostring(t)+" "+itostring(offsetauxspace)+" t"+itostring(t)||
        "pushparam t"+itostring(t);
      offsetauxspace+=child(a,0)->tp->down->down->size*child(a,0)->tp->down->down->numelemsarray;
      if (offsetauxspace > maxoffsetauxspace) maxoffsetauxspace = offsetauxspace;
      t++;
    }
    codechain cremoveparam;
    CodeGenRealParams(child(child(a, 1), 0), child(a, 0)->tp->down, cpushparam, cremoveparam, t);
    cpushparam=cpushparam||
    indirections(symboltable.jumped_scopes(child(a,0)->text),t)||
    "pushparam t"+itostring(t);
    cremoveparam=cremoveparam||"killparam";
    if (isbasickind(child(a,0)->tp->right->kind))
      cremoveparam=cremoveparam||"popparam t"+itostring(t);
    else
    {
      cremoveparam=cremoveparam||"killparam";
    }
    c=cpushparam||
      "call "+symboltable.idtable(child(a,0)->text)+"_"+child(a,0)->text||
      cremoveparam;
  }
  else
  {
    cout<<"BIG PROBLEM! No case defined for kind "<<a->kind<<endl;
  }
  
  #ifdef __DEBUG__
  cout<<"[GenRight]: Ending with node \""<<a->kind<<"\""<<endl;
  #endif
  
  return c;
}

// ...to be completed:
codechain CodeGenInstruction(AST *a,string info="")
{
  codechain c;

  if (!a) return c;
  
  #ifdef __DEBUG__
  cout<<"[CodeGenInstruction]: Starting with node \""<<a->kind<<"\""<<endl;
  #endif
  
  offsetauxspace=0;
  if (a->kind=="list")
  {
    for (AST *a1=a->down;a1!=0;a1=a1->right)
    {
      c=c||CodeGenInstruction(a1,info);
    }
  }
  else if (a->kind==":=")
  {
    if (isbasickind(child(a,0)->tp->kind))
    {
      c=GenLeft(child(a,0),0)||GenRight(child(a,1),1)||"stor t1 t0";
    }
    else if (child(a,1)->ref)
    {
      c=GenLeft(child(a,0),0)||GenLeft(child(a,1),1)||"copy t1 t0 "+itostring(child(a,1)->tp->size);
    }
    else
    {
      c=GenLeft(child(a,0),0)||GenRight(child(a,1),1)||"copy t1 t0 "+itostring(child(a,1)->tp->size);
    }
  } 
  else if (a->kind=="write" || a->kind=="writeln")
  {
    if (child(a,0)->kind=="string")
    {
      c="wris "+child(a,0)->text;
    } 
    else
    {
      //Exp
      c=GenRight(child(a,0),0)||"wrii t0";
    }

    if (a->kind=="writeln")
    {
      c=c||"wrln";
    }
  }
  else if (a->kind == "while")
  {
    int etiq = newLabelWhile();
    c="etiq while_"+itostring(etiq)||
      GenRight(child(a,0),0)||
      "fjmp t0 endwhile_"+itostring(etiq)||
      CodeGenInstruction(child(a,1),info)||
      "ujmp while_"+itostring(etiq)||
      "etiq endwhile_"+itostring(etiq);
  }
  else if (a->kind == "if")
  {
    int etiq = newLabelIf();
    c=GenRight(child(a,0),0);
    if (child(a,2))
    {
      c=c||"fjmp t0 else_"+itostring(etiq)||
        CodeGenInstruction(child(a,1),info)||
        "ujmp endif_"+itostring(etiq)||
        "etiq else_"+itostring(etiq)||
        CodeGenInstruction(child(a,2),info);
    }
    else
    {
      c=c||"fjmp t0 endif_"+itostring(etiq)||
        CodeGenInstruction(child(a,1),info);
    }
    c=c||"etiq endif_"+itostring(etiq);
  }
  else if (a->kind == "(")
  {
    codechain cpushparam, cremoveparam;
    CodeGenRealParams(child(child(a, 1), 0), child(a, 0)->tp->down, cpushparam, cremoveparam, 0);
    cpushparam=cpushparam||
    indirections(symboltable.jumped_scopes(child(a,0)->text),0)||
    "pushparam t0";
    cremoveparam=cremoveparam||"killparam";
    c=cpushparam||
      "call "+symboltable.idtable(child(a,0)->text)+"_"+child(a,0)->text||
      cremoveparam;
  }
  
  #ifdef __DEBUG__
  cout<<"[CodeGenInstruction]: Ending with node \""<<a->kind<<"\""<<endl;
  #endif

  return c;
}

void CodeGenSubroutine(AST *a,list<codesubroutine> &l)
{
  codesubroutine cs;

  #ifdef __DEBUG__
  cout<<"[CodeGenSubroutine]: Starting with node \""<<a->kind<<"\""<<endl;
  #endif
  
  string idtable=symboltable.idtable(child(a,0)->text);
  cs.name=idtable+"_"+child(a,0)->text;
  symboltable.push(a->sc);
  symboltable.setidtable(idtable+"_"+child(a,0)->text);

  gencodevariablesandsetsizes(a->sc,cs,a->kind=="function");
  for (AST *a1=child(child(a,2),0);a1!=0;a1=a1->right)
  {
    CodeGenSubroutine(a1,l);
  }
  
  maxoffsetauxspace=0;
  newLabelIf(true);
  newLabelWhile(true);
  
  cs.c=CodeGenInstruction(child(a,3));
  if (a->sc,cs,a->kind=="function")
  {
    if (isbasickind(a->tp->right->kind))
      cs.c=cs.c||
        "load _"+child(a,4)->text+" t0"||
        "stor t0 returnvalue";
    else if (a->tp->right->kind=="array")
    {
      cs.c=cs.c||
        "aload _"+child(a,4)->text+" t1"||
        "load returnvalue t0"||
        "copy t1 t0 "+itostring(a->tp->down->down->size);
    }
  }
  cs.c=cs.c||"retu";
  
  if (maxoffsetauxspace>0)
  {
    variable_data vd;
    vd.name="aux_space";
    vd.size=maxoffsetauxspace;
    cs.localvariables.push_back(vd);
  }
  
  symboltable.pop();
  l.push_back(cs);
  
  #ifdef __DEBUG__
  cout<<"[CodeGenSubroutine]: Ending with node \""<<a->kind<<"\""<<endl;
  #endif
}

void CodeGen(AST *a,codeglobal &cg)
{
  initnumops();
  securemodeon();
  cg.mainsub.name="program";
  symboltable.push(a->sc);
  symboltable.setidtable("program");
  gencodevariablesandsetsizes(a->sc,cg.mainsub);
  for (AST *a1=child(child(a,1),0);a1!=0;a1=a1->right) {
    CodeGenSubroutine(a1,cg.l);
  }
  maxoffsetauxspace=0; newLabelIf(true); newLabelWhile(true);
  cg.mainsub.c=CodeGenInstruction(child(a,2))||"stop";
  if (maxoffsetauxspace>0) {
    variable_data vd;
    vd.name="aux_space";
    vd.size=maxoffsetauxspace;
    cg.mainsub.localvariables.push_back(vd);
  }
  symboltable.pop();
}

