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

#include "myASTnode.hh"

#include "semantic.hh"

#include "util.hh"

// feedback the main program with our error status
int TypeError = 0;


/// ---------- Error reporting routines --------------

void errornumparam(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": The number of parameters in the call do not match."<<endl;
}

void errorincompatibleparam(int l,int n) {
  TypeError = 1;
  cout<<"L. "<<l<<": Parameter "<<n<<" with incompatible types."<<endl;
}

void errorreferenceableparam(int l,int n) {
  TypeError = 1;
  cout<<"L. "<<l<<": Parameter "<<n<<" is expected to be referenceable but it is not."<<endl;
}

void errordeclaredident(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Identifier "<<s<<" already declared."<<endl;
}

void errornondeclaredident(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Identifier "<<s<<" is undeclared."<<endl;
}

void errornonreferenceableleft(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Left expression of assignment is not referenceable."<<endl;
}

void errorincompatibleassignment(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Assignment with incompatible types."<<endl;
}

void errorbooleanrequired(int l,string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Instruction "<<s<<" requires a boolean condition."<<endl;
}

void errorisnotprocedure(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator ( must be applied to a procedure in an instruction."<<endl;
}

void errorisnotfunction(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator ( must be applied to a function in an expression."<<endl;
}

void errorincompatibleoperator(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Operator "<<s<<" with incompatible types."<<endl;
}

void errorincompatiblereturn(int l) {
  TypeError = 1;
  cout<<"L. "<<l<<": Return with incompatible type."<<endl;
}

void errorreadwriterequirebasic(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Basic type required in "<<s<<"."<<endl;
}

void errornonreferenceableexpression(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Referenceable expression required in "<<s<<"."<<endl;
}

void errornonfielddefined(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Field "<<s<<" is not defined in the struct."<<endl;
}

void errorfielddefined(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Field "<<s<<" already defined in the struct."<<endl;
}

void errornoshadow(int l, string s) {
  TypeError = 1;
  cout<<"L. "<<l<<": Procedure or function "<<s<<" does not hide any existing one."<<endl;
}

/// ------------------------------------------------------------
/// Table to store information about program identifiers
symtab symboltable;

static void InsertintoST(int line,string kind,string id,ptype tp)
{
  infosym p;

  if (symboltable.find(id) && symboltable.jumped_scopes(id)==0) errordeclaredident(line,id);
  else {
    symboltable.createsymbol(id);
    symboltable[id].kind=kind;
    symboltable[id].tp=tp;
  }
}

/// ------------------------------------------------------------

bool isbasickind(string kind) {
  return kind=="int" || kind=="bool";
}



void check_params(AST *a, ptype tp, int line, int numparam)
{
    int params = 0;
    for (AST *i = a; i != 0; i = i->right)
        params++;
    
    if (numparam != params)
        errornumparam(line);
    else
    {
        params = 1;
        while (a != 0)
        {
            TypeCheck(a);
            
            if (tp->kind == "parref" && (!a->ref || a->tp->kind == "procedure" || a->tp->kind == "function"))
                errorreferenceableparam(line, params);
            
            if (a->tp->kind != "error" && tp->down->kind != "error" && !equivalent_types(a->tp, tp->down))
                errorincompatibleparam(line, params);
            
            a = a->right;
            tp = tp->right;
            params++;
        }
    }
}

void insert_vars(AST *a)
{
  if (!a) return;
  TypeCheck(child(a,0));
  InsertintoST(a->line,"idvarlocal",a->text,child(a,0)->tp);
  insert_vars(a->right); 
}

void insert_params(AST *a)
{
    if (!a) return;
    InsertintoST(a->line, "idpar" + a->kind, child(a, 0)->text, child(a, 1)->tp);
    insert_params(a->right); 
}

void construct_struct(AST *a)
{
  AST *a1=child(a,0);
  a->tp=create_type("struct",0,0);

  while (a1!=0) {
    TypeCheck(child(a1,0));
    if (a->tp->struct_field.find(a1->text)==a->tp->struct_field.end()) {
      a->tp->struct_field[a1->text]=child(a1,0)->tp;
      a->tp->ids.push_back(a1->text);
     } else {
      errorfielddefined(a1->line,a1->text);
    }
    a1=a1->right;
  }
}

void construct_array(AST *a)
{
    TypeCheck(child(a, 0));
    TypeCheck(child(a, 1));
    
    a->tp = create_type("array", child(a, 1)->tp, 0);
    a->tp->numelemsarray = stringtoint(child(a, 0)->text);
}

string decoration(ptype t)
{
    if (t->kind == "int") return "i";
    if (t->kind == "bool") return "b";
    if (t->kind == "array")
    {
        string aux = "a";
        aux.append(itostring(t->numelemsarray));
        aux.append(decoration(t->down));
        return aux;
    }
    if (t->kind == "struct")
    {
        string aux = "s";
        for (list<string>::iterator it = t->ids.begin(); it != t->ids.end(); it++)
        {
            aux.append("<");
            aux.append(*it);
            aux.append(",");
            aux.append(decoration(t->struct_field[*it]));
            aux.append(">");
        }
        aux.append("e");
        return aux;
    }

    return "";
}

void create_header(AST *a)
{
    a->tp = create_type(a->kind, 0, 0);

    bool overload = false;
    
    if (a->kind == "function")
    {
        TypeCheck(child(child(a, 0), 1));
        a->tp->right = child(child(a, 0), 1)->tp;

        if (child(child(a, 0), 2) != 0)
        {
            if (child(child(a, 0), 2)->kind == "shadow" && !symboltable.find(child(a, 0)->text))
                errornoshadow(a->line, child(a, 0)->text);
            else if (child(child(a, 0), 2)->kind == "overload") overload = true;
        }
    }
    else if (child(child(a, 0), 1) != 0)
    {
        if (child(child(a, 0), 1)->kind == "shadow" && !symboltable.find(child(a, 0)->text))
            errornoshadow(a->line, child(a, 0)->text);
        else if (child(child(a, 0), 1)->kind == "overload") overload = true;
    }
    
    AST *a1 = child(child(child(a, 0), 0), 0);
    ptype prev = 0;
    int params = 0;
    string aux = "";
    while (a1 != 0)
    {
        TypeCheck(child(a1, 1));

        if (overload) aux.append(decoration(child(a1, 1)->tp));

        ptype next = create_type("par" + a1->kind, child(a1, 1)->tp, 0);
        if (prev == 0) a->tp->down = next;
        else prev->right = next;
        
        prev = next;
        params++;
        a1 = a1->right;
    }
    
    a->tp->numelemsarray = params;

    if (overload)
    {
        child(a, 0)->text.append("_");
        child(a, 0)->text.append(aux);
    }
}

void insert_header(AST *a)
{
    create_header(a);
    
    if (a->kind == "procedure")
        InsertintoST(a->line, "idproc", child(a, 0)->text, a->tp);
    else if (a->kind == "function")
        InsertintoST(a->line, "idfunc", child(a, 0)->text, a->tp);
}

void insert_headers(AST *a)
{
  while (a!=0) {
    insert_header(a);
    a=a->right;
  }
}

void TypeCheck(AST *a,string info)
{
    if (!a) return;

    /*cout<<"Starting with node \""<<a->kind<<"\""<<endl;*/

    /* KIND PROGRAM */
    if (a->kind == "program")
    {
        a->sc = symboltable.push();
        
        insert_vars(child(child(a, 0), 0));
        insert_headers(child(child(a, 1), 0));
        
        TypeCheck(child(a, 1));
        TypeCheck(child(a, 2), "instruction");
        
        symboltable.pop();
  }

    /* KIND LIST */
    else if (a->kind == "list")
    {
        /* At this point only instruction, procedures or parameters lists are possible. */
        for (AST *a1 = a->down; a1 != 0; a1 = a1->right)
            TypeCheck(a1, info);
    }

    /* KIND BASICKIND */
    else if (isbasickind(a->kind))
        a->tp = create_type(a->kind, 0, 0);

    /* KIND STRUCT */
    else if (a->kind == "struct")
        construct_struct(a);

    /* KIND ARRAY */
    else if (a->kind == "array")
        construct_array(a);

    /* KIND READ */
    else if (a->kind == "read")
    {
        TypeCheck(child(a, 0));
        
        if (child(a, 0)->tp->kind != "error")
        {
            if (!child(a, 0)->ref || child(a, 0)->tp->kind == "procedure" || child(a, 0)->tp->kind == "function")
                errornonreferenceableexpression(a->line, a->kind);
            else if (!isbasickind(child(a, 0)->tp->kind))
                errorreadwriterequirebasic(a->line, a->kind);
        }
    }

    /* KIND WRITE or WRITELN */
    else if (a->kind == "write" || a->kind == "writeln")
    {
        TypeCheck(child(a, 0));
        
        if (child(a, 0)->tp->kind != "error" && !isbasickind(child(a, 0)->tp->kind) && child(a, 0)->tp->kind != "string")
            errorreadwriterequirebasic(a->line, a->kind);
    }

    /* KIND IF */
    else if (a->kind == "if")
    {
        TypeCheck(child(a, 0));
        
        if (child(a, 0)->tp->kind != "error" && child(a, 0)->tp->kind != "bool")
            errorbooleanrequired(a->line, a->kind);
        
        /* TypeCheck Then */
        TypeCheck(child(a, 1));
        
        /* TypeCheck Else */
        TypeCheck(child(a, 2));
    }

    /* KIND WHILE */
    else if (a->kind == "while")
    {
        TypeCheck(child(a, 0));
        
        if (child(a, 0)->tp->kind != "error" && child(a, 0)->tp->kind != "bool")
            errorbooleanrequired(a->line, a->kind);
        
        TypeCheck(child(a, 1));
    }

    /* KIND PROCEDURE */
    else if(a->kind == "procedure")
    {
        a->sc = symboltable.push();
        
        insert_params(child(child(child(a, 0), 0), 0));
        insert_vars(child(child(a, 1), 0));
        insert_headers(child(child(a, 2), 0));
        
        TypeCheck(child(a, 2));
        TypeCheck(child(a, 3), "instruction");
        
        symboltable.pop();
    }

    /* KIND FUNCTION */
    else if(a->kind == "function")
    {
        a->sc = symboltable.push();
        
        insert_params(child(child(child(a, 0), 0), 0));
        insert_vars(child(child(a, 1), 0));
        insert_headers(child(child(a, 2), 0));
        
        TypeCheck(child(a, 2));
        TypeCheck(child(a, 3), "instruction");
        TypeCheck(child(a, 4));
        
        if (child(a, 4)->tp->kind != "error" && child(child(a, 0), 1)->tp->kind != "error" && !equivalent_types(child(a, 4)->tp, child(child(a, 0), 1)->tp))
            errorincompatiblereturn(child(a, 4)->line);
        
        symboltable.pop();
    }

    /* KIND AND or OR */
    else if (a->kind == "and" || a->kind == "or")
    {
        TypeCheck(child(a, 0));
        TypeCheck(child(a, 1));
        
        if ((child(a, 0)->tp->kind != "error" && child(a, 0)->tp->kind != "bool") || (child(a, 1)->tp->kind != "error" && child(a, 1)->tp->kind != "bool"))
            errorincompatibleoperator(a->line, a->kind);
        
        a->tp = create_type("bool", 0, 0);
    }

    /* KIND EQUAL */
    else if (a->kind == "=")
    {
        TypeCheck(child(a, 0));
        TypeCheck(child(a, 1));
        
        if (child(a, 0)->tp->kind != "error" && child(a, 1)->tp->kind != "error" && (!isbasickind(child(a, 0)->tp->kind) || !equivalent_types(child(a, 0)->tp, child(a, 1)->tp)))
            errorincompatibleoperator(a->line, a->kind );
        
        a->tp = create_type("bool", 0, 0);
    }

    /* KIND GTHAN or LTHAN */
    else if (a->kind == ">" || a->kind == "<")
    {
        TypeCheck(child(a, 0));
        TypeCheck(child(a, 1));
        
        if (child(a, 0)->tp->kind != "error" && child(a, 1)->tp->kind != "error" && (child(a, 0)->tp->kind != "int" || !equivalent_types(child(a, 0)->tp, child(a, 1)->tp)))
            errorincompatibleoperator(a->line, a->kind );
        
        a->tp = create_type("bool", 0, 0);
    }

    /* KIND PLUS, MINUS, TIMES or DIV */
    else if (a->kind == "+" || (a->kind == "-" && child(a, 1) != 0) || a->kind=="*" || a->kind=="/")
    {
        TypeCheck(child(a, 0));
        TypeCheck(child(a, 1));
        
        if ((child(a, 0)->tp->kind != "error" && child(a, 0)->tp->kind != "int") || (child(a, 1)->tp->kind != "error" && child(a, 1)->tp->kind != "int"))
            errorincompatibleoperator(a->line, a->kind);
        
        a->tp = create_type("int", 0, 0);
    }

    /* KIND MINUS (UNARY) */
    else if (a->kind == "-" && child(a, 1) == 0)
    {
        TypeCheck(child(a, 0));
        
        if (child(a, 0)->tp->kind != "error" && child(a, 0)->tp->kind != "int")
            errorincompatibleoperator(a->line, a->kind);
        
        a->tp = create_type("int", 0, 0);
    }

    /* KIND NOT */
    else if (a->kind == "not")
    {
      TypeCheck(child(a, 0));
      
      if (child(a, 0)->tp->kind != "error" && child(a, 0)->tp->kind != "bool")
          errorincompatibleoperator(a->line, a->kind);
      
      a->tp = create_type("bool", 0, 0);
    }

    /* KIND OPENPAR */
    else if (a->kind == "(")
    {
        if (!symboltable.find(child(a, 0)->text))
        {
            string aux = "";
            AST *aaux = child(child(a, 1), 0);
            while (aaux != 0)
            {
                TypeCheck(aaux);
                aux.append(decoration(aaux->tp));
                aaux = aaux->right;
            }
            
            string aux2 = child(a, 0)->text;
            aux2.append("_");
            aux2.append(aux);

            if (symboltable.find(aux2)) child(a, 0)->text = aux2;
        }
        
        TypeCheck(child(a, 0));
        
        if (child(a, 0)->tp->kind != "error")
        {
            if (child(a, 0)->tp->kind == "procedure" || child(a, 0)->tp->kind == "function")
            {
                if (info == "instruction")
                {
                    if (child(a, 0)->tp->kind != "procedure")
                        errorisnotprocedure(a->line);
                }
                else
                {
                    if (child(a, 0)->tp->kind != "function")
                        errorisnotfunction(a->line);
                    else a->tp = child(a, 0)->tp->right;
                }
                check_params(child(child(a, 1), 0), child(a, 0)->tp->down, a->line, child(a, 0)->tp->numelemsarray);
            }
            else if (info == "instruction")
                errorisnotprocedure(a->line);
            else errorisnotfunction(a->line);
        }
    }

    /* KIND OPENCLASP */
    else if (a->kind == "[")
    {
        TypeCheck(child(a, 0));
        TypeCheck(child(a, 1));
        
        a->ref = child(a, 0)->ref;
        
        if (child(a, 0)->tp->kind != "error")
        {
            if (child(a, 0)->tp->kind != "array")
                errorincompatibleoperator(a->line, "array[]");
            else a->tp =  child(a, 0)->tp->down;
        }
        
        if (child(a, 1)->tp->kind != "error" && child(a, 1)->tp->kind != "int")
            errorincompatibleoperator(a->line, "[]");
    }

    /* KIND ASIG */
    else if (a->kind == ":=")
    {
        TypeCheck(child(a, 0));
        TypeCheck(child(a, 1));
        
        if (!child(a, 0)->ref || child(a, 0)->tp->kind == "procedure" || child(a, 0)->tp->kind == "function")
            errornonreferenceableleft(a->line, child(a, 0)->text);
        else if (child(a, 0)->tp->kind!="error" && child(a, 1)->tp->kind!="error" && !equivalent_types(child(a, 0)->tp, child(a, 1)->tp))
            errorincompatibleassignment(a->line);
        else a->tp = child(a, 0)->tp;
    }

    /* KIND STRUCT DOT */
    else if (a->kind==".")
    {
        TypeCheck(child(a, 0));
        a->ref = child(a, 0)->ref;
        
        if (child(a, 0)->tp->kind != "error")
        {
            if (child(a, 0)->tp->kind != "struct")
                errorincompatibleoperator(a->line,"struct.");
            else if (child(a, 0)->tp->struct_field.find(child(a, 1)->text) == child(a, 0)->tp->struct_field.end())
                errornonfielddefined(a->line,child(a, 1)->text);
            else a->tp = child(a, 0)->tp->struct_field[child(a, 1)->text];
        }
    }
    
    /* KIND STRING */
    else if(a->kind == "string")
        a->tp = create_type("string", 0, 0);

    /* KIND INTCONST */
    else if (a->kind == "intconst")
        a->tp = create_type("int", 0, 0);

    /* KIND BOOLCONST */
    else if (a->kind == "true" || a->kind == "false")
        a->tp=create_type("bool", 0, 0);

    /* KIND IDENT */
    else if (a->kind == "ident")
    {
        if (!symboltable.find(a->text))
            errornondeclaredident(a->line, a->text);
        else
        {
            a->tp = symboltable[a->text].tp;
            a->ref = 1;
        }
    }

    /* NOT DEFINED KIND */
    else cout<<"BIG PROBLEM! No case defined for kind "<<a->kind<<endl;

    //cout<<"Ending with node \""<<a->kind<<"\""<<endl;
}
