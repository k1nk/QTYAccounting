# Copyright (c) 2022 Kenichi Nakatani
# This file is part of QTYAccounting.
# QTYAccounting is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
# QTYAccounting is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
# You should have received a copy of the GNU General Public License along with QTYAccounting. If not, see <https://www.gnu.org/licenses/>.

import os
import csv
import json
import pandas as pd
import datetime
from lark import Lark
from lark import Transformer
from lark import Tree,Token
from itertools import zip_longest
from lark.visitors import Interpreter
from pathlib import Path
from collections import deque
from ast import literal_eval

class QTYJournalToTree:
    """
    １つ以上の数量簿記の仕訳（journal_entry）を含む仕訳帳（journal、テキスト形式）を解析して構文木を作成する。

    journal_strは仕訳帳（journal）および仕訳（journal_entry）の定義を表わす。
    lark_def_strは、仕訳（journal_entry）の構成要素の定義を表わす。
    datetime_def_strは、特に日時の定義を表す。日時は、ISO 8601に準拠した形式としている。
    """

    ## ver20230714 accept ref_memo with param. change quote char of ref_memo  from "<>" to "[]"
    ## ver20230721 add weight _REF_START_MARK _REF_END_MARK
    ##             devide PARENTHESIS to PARENTHESIS and PARENTHESIS_MARK
    ##             devide SLASH to SLASH and SLASH_MARK
    ## common definition
    lark_def_str = r"""    
        datetime: DATETIME
        prefixed_time: PREFIXED_TIME
        time_zone: TIME_ZONE
        
        account: STRING
        sub_account: STRING | ref_memo
        item: STRING | ref_memo
        
        ref_memo: _REF_START_MARK STRING _REF_END_MARK
        price: number | ref_memo
        price_unit: STRING_AND_MARK_WITHOUT_DIGIT
    
        quantity: number | op_quantity | ref_memo
        op_quantity: OP_EQUAL_QUANTITY | OP_BALANCE_QUANTITY | OP_DIFF_QUANTITY
        quantity_unit: STRING_AND_MARK_WITHOUT_DIGIT
        
        amount: number | op_amount | ref_memo
        op_amount: OP_AUTO_AMOUNT | OP_BALANCE_AMOUNT | OP_DIFF_AMOUNT | OP_EQUAL_AMOUNT
        amount_unit: STRING_AND_MARK_WITHOUT_DIGIT
        
        memo_number: key ":" number memo_unit?
        memo_string: key "::" STRING
        key: STRING
        memo_unit: STRING_AND_MARK_WITHOUT_DIGIT
        
        _DEBIT_SIGN.10: "Dr" | "借方"
        _CREDIT_SIGN.10: "Cr" | "貸方"
        
        param_mark: PARTNER_MARK | PERSON_IN_CHARGE_MARK | MEMO_MARK | REMARKS_MARK
        param: string | memo_number | memo_string | ref_memo
        param_pair: param_mark param
        
        _REF_START_MARK.5: "["
        _REF_END_MARK.5: "]"
        _ENTRY_START_MARK.10: "<<"
        _SUB_ACCOUNT_MARK.5: "/"
        _ITEM_MARK.5: "#"
        _PRICE_MARK.5: "@"
        _QUANTITY_MARK.5: "*"
        PARTNER_MARK.5: "$"
        PERSON_IN_CHARGE_MARK.5: ">"
        MEMO_MARK.5: "&"
        REMARKS_MARK.10: "##"
        _ENTRY_END_MARK.10: ">>"
        
        OP_AUTO_AMOUNT.9: "?" | "?A"
        OP_BALANCE_AMOUNT.10: "?B"
        OP_DIFF_AMOUNT.10: "?D"
        OP_EQUAL_AMOUNT.10: "?E"
        
        OP_EQUAL_QUANTITY.9:"E"
        OP_BALANCE_QUANTITY.9:"B"
        OP_DIFF_QUANTITY.9:"D"

        DIGIT: "0".."9" // \u0020-\u0029
        INT: DIGIT+
        number: NUMBER
        NUMBER: ["+"|"-"] INT ((","|"_") INT)* ["." INT]
        
        TEXT_WITHOUT_SLASH: /[\u0011-\u002E\u0030-\uFFFF]+/
        TEXT_WITHOUT_SLASH_QUOTE_COMMA: /[\u0011-\u0021\u0023-\u0026\u0028-\u002B\u002D-\u002E\u0030-\uFFFF]+/
        
        string:STRING
        
        PARENTHESIS: "(" | ")" | "（" | "）" | "［" | "］"
        PARENTHESIS_MARK: "[" | "]"
        SLASH: "／"
        SLASH_MARK: "/"
        MIDDLE_DOT: "･" | "・"
        UNDER_SCORE: "_" | "＿"     
        KUTEN_KIGOU:/[\u3001-\u3030]+/
        HIRAGANA: /[\u3041-\u3096\u3099-\u309F]+/
        KATAKANA: /[\u30A1-\u30FF]+/
        KAKOMI: /[\u3200-\u32FF]+/
        ZENKAKU_DIGIT: /[\uFF10-\uFF19]+/

        KIGOU: "!" | "#".."+" | "-".."/"
        ZENKAKU_KIGOU: /[\uFF01-\uFF0F\uFF1A-\uFF20\uFF3B-\uFF40\uFF5B-\uFF65]+/
        ZENKAKU_ALPHABET: /[\uFF21-\uFF3A\uFF41-\uFF5A]+/
        ZENKAKU_KATAKANA: /[\uFF66-\uFF9F]+/

        KANJI: /[〻\u3400-\u9FFF\uF900-\uFAFF]|[\uD840-\uD87F][\uDC00-\uDFFF]+/
        STRING: (UNDER_SCORE|LETTER|DIGIT|"."|HIRAGANA|KATAKANA|KANJI|ZENKAKU_DIGIT|ZENKAKU_KIGOU|ZENKAKU_ALPHABET|ZENKAKU_KATAKANA|MIDDLE_DOT|KUTEN_KIGOU|KAKOMI|SLASH|PARENTHESIS)+
        STRING_AND_MARK: (UNDER_SCORE|LETTER|DIGIT|"."|HIRAGANA|KATAKANA|KANJI|ZENKAKU_DIGIT|ZENKAKU_KIGOU|ZENKAKU_ALPHABET|ZENKAKU_KATAKANA|MIDDLE_DOT|KUTEN_KIGOU|KAKOMI|SLASH|SLASH_MARK|PARENTHESIS|PARENTHESIS_MARK)+
        STRING_AND_MARK_WITHOUT_DIGIT: (UNDER_SCORE|LETTER|HIRAGANA|KATAKANA|KANJI|ZENKAKU_KIGOU|ZENKAKU_ALPHABET|ZENKAKU_KATAKANA|MIDDLE_DOT|KUTEN_KIGOU|KAKOMI|SLASH|SLASH_MARK|PARENTHESIS|PARENTHESIS_MARK)+
        STRING_AND_MARK2: (KIGOU|","|"|"|"~"|";"|"="|" "|":"|"　"|UNDER_SCORE|LETTER|DIGIT|"."|HIRAGANA|KATAKANA|KANJI|ZENKAKU_DIGIT|ZENKAKU_KIGOU|ZENKAKU_ALPHABET|ZENKAKU_KATAKANA|MIDDLE_DOT|KUTEN_KIGOU|KAKOMI|SLASH|SLASH_MARK|PARENTHESIS|PARENTHESIS_MARK)+
        
        WS2: /[ \t\f\r\n　]/+ // HANKAKU space,Horizontal TAB,Form Feed,Carriage Return,Line Feed,ZENKAKU space
        WS3: /[ \t　]/+ // HANKAKU space,Horizontal TAB,ZENKAKU space

        LCASE_LETTER: "a".."z" // \u0031-\u004A
        UCASE_LETTER: "A".."Z" // \u0051-\u006A
        LETTER: UCASE_LETTER | LCASE_LETTER
        
        """
    
    datetime_def_str = r"""  
        YEAR  : DIGIT DIGIT DIGIT DIGIT
        MONTH : "0" "1".."9"
            | "1" "0".."2" 
        DAY   : "0" DIGIT
            | "1" DIGIT 
            | "2" DIGIT
            | "3" "0".."1" 

        HOUR   : "0".."1" DIGIT
            | "2" "0".."4"
        MINUTE : "0".."5" DIGIT
        SECOND : "0".."5" DIGIT 
            | "60"
        AFTER_DECIMAL : "." DIGIT+

        DATE : YEAR "-"? MONTH "-"? DAY
        PREFIXED_TIME : "T" HOUR ":"? MINUTE ":"? SECOND AFTER_DECIMAL?
        TIME_ZONE : "Z"
                | ("+"|"-") HOUR (":"? MINUTE)
            
        DATETIME : DATE PREFIXED_TIME? TIME_ZONE?
        """

    journal_str = r"""
        journal: (text* journal_entry)* text*
        journal_entry: entry_header (debit | credit)* entry_footer
        entry_header: _ENTRY_START_MARK  datetime param_pair*
        debit:  _DEBIT_SIGN   account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        credit: _CREDIT_SIGN  account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        entry_footer: _ENTRY_END_MARK
        
        text: TEXT
        TEXT: /[\u0011-\uFFFF]+/
        %ignore WS2
        """

    def __init__(self):

        ## ver20230610
        ## definition of journal_entry
        ## definition of journal(plain text document that include journal entries and texts)
        ##

        #journal_entry_parser_lalr = Lark(journal_str+lark_def_str+datetime_def_str,start ="journal_entry",parser='lalr')
        #tree_entry = journal_entry_parser_lalr.parse(journal_entry2)

        self.journal_parser_lalr = Lark(self.journal_str+self.lark_def_str+self.datetime_def_str,start ="journal",parser='lalr')
    
    def translate(self,journal):
        """
        仕訳帳（journal）を解析(prase)して構文木を返す。

        Parameters
        ----------
        journal : str
            仕訳帳

        Returns
        -------
        tree : Tree
            構文木
        """
        tree = self.journal_parser_lalr.parse(journal)
        return tree

class CalculateTree(Transformer):
    # 変換のための基本となるクラス
    #def __init__(self):
    #    pass

    def get_updated_dict_with_param_pair(self,original_dict,child):
        
        if type(child) is not tuple:
            return original_dict
        
        if type(original_dict) is not dict:
            return original_dict
        
        target_dict = original_dict.copy()
        
        param_mark,param = child
        if param_mark=="MEMO_MARK" and type(param) is dict:
            
            if "memo_number" in param:
                # param
                # {"memo_number",{"温度":(12,"度")}}
                if "memo" in target_dict:
                    target_dict["memo"].update(param["memo_number"])
                else:
                    target_dict["memo"]=param["memo_number"]
                #if "memo_number" in target_dict:
                #    target_dict["memo_number"].append(param["memo_number"])
                #else:
                #    target_dict["memo_number"]=[param["memo_number"]]
            elif "memo_string" in param:
                #{"memo_string",{"天気":"晴れ"}}
                if "memo" in target_dict:
                    target_dict["memo"].update(param["memo_string"])
                else:
                    target_dict["memo"]=param["memo_string"]
                #if "memo_string" in target_dict:
                #    target_dict["memo_string"].append(param["memo_string"])
                #else:
                #    target_dict["memo_string"]=[param["memo_string"]]
            else:
                pass
        elif param_mark=="PARTNER_MARK":
            target_dict.update({"partner":param})
        elif param_mark=="PERSON_IN_CHARGE_MARK":
            target_dict.update({"person_in_charge":param})
        elif param_mark=="REMARKS_MARK":
            target_dict.update({"remarks":param})                    
        else:
            pass
        return target_dict
    

    def datetime(self, children):
        #datetime: DATETIME
        return {"datetime":(children[0].type,children[0].value)}

    def prefixed_time(self,children):
        return {"prefixed_time":children[0].value}
    
    def time_zone(self,children):
        return {"time_zone":children[0].value}
    
    def account(self, children):
        #account: STRING
        
        return {"account":children[0].value}

    def sub_account(self, children):
        #sub_account: STRING | ref_memo
        #print(children[0])
        if type(children[0]) is dict:
            #ref_memo
            return {"sub_account":children[0]}
        else:
            #STRING
            return {"sub_account":children[0].value}
    
    def item(self, children):
        #item: STRING | ref_memo
        if type(children[0]) is dict:
            #ref_memo
            return {"item":children[0]}
        else:
            #STRING
            return {"item":children[0].value}

    def price(self, children):
        #price: number | ref_memo
        return {"price":children[0]}
    
    def price_unit(self, children):
        #price_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return {"price_unit":children[0].value}

    def op_quantity(self, children):
        #op_quantity: OP_EQUAL_QUANTITY | OP_BALANCE_QUANTITY | OP_DIFF_QUANTITY
        #if type(children[0])
        return {"op_quantity":children[0].type}

    def quantity(self, children):
        #quantity: number | op_quantity | ref_memo
        #print("quantity")
        #print(type(children[0]))
        if type(children[0]) is dict:
            if "op_quantity" in children[0]:
                #op_quantity
                ##print(children[0])
                ## example {'op_quantity': 'OP_EQUAL_QUANTITY'}
                #return children[0]
                return {"quantity":children[0]}
            else:
                #ref_memo
                #return {"op_quantity":"OP_REF_QUANTITY","quantity":children[0]}
                return {"quantity":children[0]}
        else:
            #number
            #return {"op_quantity":"OP_VALUE_QUANTITY","quantity":children[0]}
            return {"quantity":children[0]}

        return children
    
    def quantity_unit(self, children):
        #quantity_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return {"quantity_unit":children[0].value}
    
    def op_amount(self, children):
        #op_amount: OP_AUTO_AMOUNT | OP_BALANCE_AMOUNT | OP_DIFF_AMOUNT
        return {"op_amount":children[0].type}

    def amount(self, children):
        #amount: number | op_amount | ref_memo
        if type(children[0]) is dict:
            if "op_amount" in  children[0]:
                #op_amount
                ##print(children[0])
                ## example {'op_amount': 'OP_EQUAL_AMOUNT'}
                #return children[0]
                return {"amount":children[0]}
            else:
                #ref_memo
                #return {"op_amount":"OP_REF_AMOUNT","amount":children[0]}
                return {"amount":children[0]}
        else:
            #number
            #return {"op_amount":"OP_VALUE_AMOUNT","amount":children[0]}
            return {"amount":children[0]}

    def amount_unit(self, children):
        #amount_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return {"amount_unit":children[0].value}
    
    def param_pair(self, children):
        #param_pair: param_mark param
        #("PARTNER_MARK","ABC商会")
        #("MEMO_MARK","ABC商会")
        #print("param_pair;",children)
        return (children[0],children[1])
    
    def param_mark(self, children):
        #param_mark: PARTNER_MARK | PERSON_IN_CHARGE_MARK | MEMO_MARK | REMARKS_MARK
        #print("param_mark",children)
        type = children[0].type
        return type
        
    def param(self, children):
        #param: string | memo_number | memo_string | ref_memo
        #print("param:",children)
        return children[0]
    
    def ref_memo(self, children):
        return {"ref_memo":children[0].value}
    
    def memo_number(self, children):
        #memo_number: key ":" number memo_unit?
        unit_str = None
        if len(children)>=3:
            unit_str = children[2]
        #print("memo_number",children)
        #return {"memo_number":(children[0],children[1],unit_str)}
        return {"memo_number":{children[0]:(children[1],unit_str)}}
    
    def memo_string(self, children):
        #memo_string: key "::" STRING
        #print("memo_string",children)
        #return {"memo_string":(children[0],children[1].value)}
        return {"memo_string":{children[0]:children[1].value}}
    
    def memo_unit(self, children):
        #memo_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return children[0].value
    
    def key(self, children):
        #key: STRING
        return children[0].value

    def number(self,children):
        #number: NUMBER
        #remove ',' and '_'
        #if number contains '.' then return float value, else return int value.
        value_str = children[0].value
        value_str_rm = value_str.translate(str.maketrans({',': None, '_': None}))
        if "." in value_str:
            ##float
            value = float(value_str_rm)
        else:
            ##int
            value = int(value_str_rm)
        return value
    
    def string(self,children):
        #string:STRING
        value = children[0].value
        return value
    
    def text(self,children):
        #text: STRING_AND_MARK
        value = children[0].value
        return value
    
class QTYJournalTreeToDic(CalculateTree):
    # Journalやjournal_entryを変換するためのクラス
    def __init__(self):
    #    super().__init__()
        #self.entry_id = 0 #仕訳番号
        #self.order_id = 0 #仕訳の中の順序
        #self.debit_line_no = 0 #行番号
        #self.credit_line_no = 0 #行番号
        self.default_json_filename="QTYjournalDic.json"
        
    def save_json(self,tree_journal,filename=None):
        
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), ACCOUNT_INFO_FILENAME)
            filename = os.path.join(Path().resolve(), self.default_json_filename)
    
        journal_dic = self.transform(tree_journal)
        
        with open(filename, 'w', newline=None,encoding='utf-8') as f:
            json.dump(journal_dic,f,ensure_ascii=False,indent=2)
            
    #    def load_json(self,filename=None):
    #        if filename is None:
    #            # filename = os.path.join(os.path.dirname(__file__), ACCOUNT_INFO_FILENAME)
    #            filename = os.path.join(Path().resolve(), self.default_json_filename)
    #        with open(filename, 'r', newline=None,encoding='utf-8') as f:
    #            journal_dic = json.load(f)
    #            
    #        return journal_dic
    
    def journal(self,children):
        #print("journal")
        journal = []
        #journal: (text* journal_entry)* text*
        for child in children:
            #print("child:",child)
            #if type(child) is dict:
            journal.append(child)
            
        #self.entry_id = 0 #仕訳番号
        return {"journal":journal}
    
    def journal_entry(self,children):
        #journal_entry: entry_header (debit | credit)+ entry_footer
        #print("journal_entry:")
        #journal_entry = {"entries":[]}
        #journal_entry = {"debit":[],"credit":[]}
        journal_entry = {}

        for child in children:
            #print("child:",child)
            if type(child) is dict:
                if "entry_header" in child:
                    journal_entry.update(child)
                    #entry_id
                    #journal_entry["entry_header"].update({"entry_id":self.entry_id})
                elif "entry_footer" in child:
                    journal_entry.update(child)
                else:
                    #debit credit
                    if "body" in journal_entry:
                        journal_entry["body"].append(child)
                    else:
                        journal_entry["body"]=[child]
      
        #reset for next journal_entry
        #self.entry_id +=1
        #self.order_id = 0 #仕訳の中の順序
        #self.debit_line_no = 0 #行番号
        #self.credit_line_no = 0 #行番号
        return  {"journal_entry":journal_entry}

    def entry_header(self,children):
        #entry_header: _ENTRY_START_MARK  datetime param_pair*
       # header = {"memo_number":[],"memo_string":[]}
        header = {}
        #print("entry_header")
        #print(len(children))
        for child in children:
            #print(type(child))
            #PARTNER_MARK | PERSON_IN_CHARGE_MARK | MEMO_MARK | REMARKS_MARK
            if type(child) is tuple:
                #param_pair
                #print("header before:",header)
                #print("child:",child)
                header = self.get_updated_dict_with_param_pair(header,child)
                #print("header after:",header)
            elif type(child) is dict:
                #datetime
                #{"datetime":('DATE','2022-12-14')}
                header.update(child)
            else:
                pass
            
        return {"entry_header":header}
    
    def debit(self,children):
        #debit:  DEBIT_SIGN   account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        #print("debit")
        #debit = {"memo_number":[],"memo_string":[]}
        debit = {}
        for child in children:
            if type(child) is tuple:
                #param_pair
                debit = self.get_updated_dict_with_param_pair(debit,child)
            elif type(child) is dict:
                #account item price quantity quantity_unit amount amount_unit
                debit.update(child)
        #if "op_amount" not in debit:
        #    debit.update({"op_amount":"OP_EQUAL_AMOUNT"})
            
        #order_id
        #debit.update({"order_id":self.order_id})
        #self.order_id +=1        
        #line_no
        #debit.update({"line_no":self.debit_line_no})
        #self.debit_line_no +=1
        
        return {"debit":debit}

    def credit(self,children):
        #print("credit")
        #credit: CREDIT_SIGN  account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        #credit = {"memo_number":[],"memo_string":[]}
        credit = {}
        for child in children:
            if type(child) is tuple:
                #param_pair
                #print("credit before:",credit)
                #print("child:",child)
                credit = self.get_updated_dict_with_param_pair(credit,child)
                #print("credit after:",credit)
            elif type(child) is dict:
                #account item price quantity quantity_unit amount amount_unit
                credit.update(child)
        #if "op_amount" not in credit:
        #    credit.update({"op_amount":"OP_EQUAL_AMOUNT"})

        #order_id
        #credit.update({"order_id":self.order_id})
        #self.order_id +=1
        #line_no
        #credit.update({"line_no":self.credit_line_no})
        #self.credit_line_no +=1

        return {"credit":credit}

    def entry_footer(self,children):
        #print("entry_footer")
        #entry_footer: _ENTRY_END_MARK
        footer = {}
        #print(len(children))
        for child in children:
           #print(type(child))
            if type(child) is tuple:
                #param_pair
                footer = self.get_updated_dict_with_param_pair(footer,child)
            elif type(child) is dict:
                footer.update(child)
        return {"entry_footer":footer}

class AccountInfo:
    # 勘定科目・補助科目・アイテムの借方・貸方の別や評価方法を管理するためのクラス
    # 直下にあるファイル（self.account_info_filename）に設定を保存・読み込み
    # 上記ファイルを直接編集して、設定を読み込んでもよい

    # 借方・貸方
    # Dr: 借方
    # Cr: 貸方
    
    # method 払出し価額計算時の計算方法
    # LPC: Last purchase cost method  最終仕入原価法
    # MA: moving average method 移動平均法
    # PA: Periodic Average Method 総平均法
    # FIFO first-in, first-out method 先入先出法
    
    def __init__(self):
        self.account_info_filename ="account_info.csv"
        self.default_method ="LPC" #評価方法を指定しない場合
        self.default_side ="Dr" # 借方・貸方を指定しない場合
        self.default_prop={"method":"LPC","side":"Dr","tax_cat":"UNDEFINED","disp_cat":"UNDEFINED"}
        self.item_info = {}
        #key:(account,sub_account,item) sub_accountを指定しない場合は"" itemを指定しない場合は""
        #value:{"side":side,"method":method,"tax_cat":tax_cat,"disp_cat":disp_cat} 
        self.load()
        
    #def set_default_method(self,method):
    #    if method in ["LPC","MA","PA","FIFO"]:
    #        #self.default_method = method
    #        self.default_prop["method"]=method

    #def get_default_method(self):
    #    #return self.default_method
    #    return self.default_prop["method"]

    def get_item_prop(self,account,sub_account,item,prop_key):
        prop_value = self.get_item_prop_overridden(account,sub_account,item,prop_key)
        if prop_value =="":
            return self.default_prop.get(prop_key,None)
        return prop_value

    def get_item_prop_overridden(self,account,sub_account,item,prop_key):
        prop_value = self.get_item_prop_raw(account,sub_account,item,prop_key)
        if prop_value is not None:
            return prop_value
        prop_value = self.get_item_prop_raw(account,sub_account,"",prop_key)
        if prop_value is not None:
            return prop_value
        prop_value = self.get_item_prop_raw(account,"","",prop_key)
        if prop_value is not None:
            return prop_value        
        return self.default_prop.get(prop_key,None)
    
    def get_item_prop_raw(self,account,sub_account,item,prop_key):
        item_info = self.item_info.get((account,sub_account,item),None)
        if item_info is None:
            return None
        prop_value = item_info.get(prop_key,None)
        if prop_value is None:
            return None
        return prop_value
    
    def get_item_method(self,account,sub_account=None,item=None):
        return self.get_item_prop(account,sub_account,item,"method")
    
    def get_item_side(self,account,sub_account=None,item=None):
        return self.get_item_prop(account,sub_account,item,"side") 

    def get_item_tax_cat(self,account,sub_account=None,item=None):
        return self.get_item_prop(account,sub_account,item,"tax_cat")

    def get_item_disp_cat(self,account,sub_account=None,item=None):
        return self.get_item_prop(account,sub_account,item,"disp_cat")

    def set_item_info(self,account,sub_account="",item="",side=None,method=None,tax_cat=None,disp_cat=None):
        #補助科目指定なしの場合は""
        #item指定なしの場合は""
        #print("set_item_info")
        #print("account:",account,"sub_account:",sub_account,"item:",item,"side:",side,"method:",method,"tax_cat:",tax_cat,"disp_cat:",disp_cat)
        if account is None:
            return
        if sub_account is None:
            return
        #sub_account can be ""
        if item is None:
            return    
        if side not in ["Dr","Cr",None,""]: # None:do not change
            return
        if method not in ["LPC","MA","PA","FIFO",None,""]: # None:do not change
            return
        
        #TAX_CAT_LIST=[None,"",'課売_10%','課売_10%_一種','課売_10%_二種','課売_10%_三種','課売_10%_四種','課売_10%_五種','課売_10%_六種','課売_(軽)8%','課売_(軽)8%_一種','課売_(軽)8%_二種','課売_(軽)8%_三種','課売_(軽)8%_四種','課売_(軽)8%_五種','課売_(軽)8%_六種','課売8%','課売8%一種','課売8%二種','課売8%三種','課売8%四種','課売8%五種','課売8%六種','課売5%','課売5%一種','課売5%二種','課売5%三種','課売5%四種','課売5%五種','課売5%六種','輸売_0%','非売','非売-有証','非輸','対象外売','課売-返還_10%','課売-返還_10%_一種','課売-返還_10%_二種','課売-返還_10%_三種','課売-返還_10%_四種','課売-返還_10%_五種','課売-返還_10%_六種','課売-返還_(軽)8%','課売-返還_(軽)8%_一種','課売-返還_(軽)8%_二種','課売-返還_(軽)8%_三種','課売-返還_(軽)8%_四種','課売-返還_(軽)8%_五種','課売-返還_(軽)8%_六種','課売-返還8%','課売-返還8%一種','課売-返還8%二種','課売-返還8%三種','課売-返還8%四種','課売-返還8%五種','課売-返還8%六種','課売-返還5%','課売-返還5%一種','課売-返還5%二種','課売-返還5%三種','課売-返還5%四種','課売-返還5%五種','課売-返還5%六種','輸売-返還_0%','非売-返還','非輸-返還','課売-貸倒_10%','課売-貸倒_(軽)8%','課売-貸倒8%','課売-貸倒5%','課売-貸倒0%','非売-貸倒','非輸-貸倒','課売-回収_10%','課売-回収_(軽)8%','課売-回収8%','課売-回収5%','課仕_10%','共-課仕_10%','非-課仕_10%','課仕_(軽)8%','共-課仕_(軽)8%','非-課仕_(軽)8%','課仕_8%','共-課仕_8%','非-課仕_8%','課仕_5%','共-課仕_5%','非-課仕_5%','輸仕-本体_10%','輸仕-消税_7.8%','輸仕-地税_2.2%','共-輸仕_10%','共-輸仕-消税_7.8%','共-輸仕-地税_2.2%','非-輸仕_10%','非-輸仕-消税_7.8%','非-輸仕-地税_2.2%','輸仕_(軽)8%','輸仕-消税_(軽)6.24%','輸仕-地税_(軽)1.76%','共-輸仕_(軽)8%','共-輸仕-消税_(軽)6.24%','共-輸仕-地税_(軽)1.76%','非-輸仕_(軽)8%','非-輸仕-消税_(軽)6.24%','非-輸仕-地税_(軽)1.76%','輸仕-本体8%','輸仕-消税6.3%','輸仕-地税1.7%','共-輸仕-本体8%','共-輸仕-消税6.3%','共-輸仕-地税1.7%','非-輸仕-本体8%','非-輸仕-消税6.3%','非-輸仕-地税1.7%','輸仕-本体5%','輸仕-消税4%','輸仕-地税1%','共-輸仕-本体5%','共-輸仕-消税4%','共-輸仕-地税1%','非-輸仕-本体5%','非-輸仕-消税4%','非-輸仕-地税1%','特定課仕_10%','共-特定課仕_10%','非-特定課仕_10%','特定課仕_8%','共-特定課仕_8%','非-特定課仕_8%','非仕','対象外仕','課仕-返還_10%','共-課仕-返還_10%','非-課仕-返還_10%','課仕-返還_(軽)8%','共-課仕-返還_(軽)8%','非-課仕-返還_(軽)8%','課仕返還_8%','共-課仕返還_8%','非-課仕返還_8%','課仕返還_5%','共-課仕返還_5%','非-課仕返還_5%','特定課仕-返還_10%','共-特定課仕-返還_10%','非-特定課仕-返還_10%','特定課仕返還_8%','共-特定課仕返還_8%','非-特定課仕返還_8%','非仕','対象外仕']
        #if tax_cat not in TAX_CAT_LIST:
        #    return

        #DISP_CAT_LIST =[None,"","貸借対照表_資産_流動資産",..."損益計算書_販売費及び一般管理費",...]
        #if disp_cat not in DISP_CAT_LIST: # None:do not change
        #    return
        
        old_info = self.item_info.get((account,sub_account,item),None)
        if old_info is None:
            self.item_info[(account,sub_account,item)]={}
        #print("old_info",old_info)
        
        if side is not None:
            updated_info = {"side":side}
            self.item_info[(account,sub_account,item)].update(updated_info)
        if method is not None:
            updated_info = {"method":method}
            self.item_info[(account,sub_account,item)].update(updated_info)
        if tax_cat is not None:
            updated_info = {"tax_cat":tax_cat}
            self.item_info[(account,sub_account,item)].update(updated_info)
        if disp_cat is not None:
            updated_info = {"disp_cat":disp_cat}
            self.item_info[(account,sub_account,item)].update(updated_info)
        #print(self.item_info)
        
    def remove_item_info_all(self,account,sub_account,item):
        self.item_info[(account,sub_account,item)]={}

    def load(self,filename=None):
        if filename is None:
            #filename = os.path.join(os.path.dirname(__file__), self.account_info_filename)
            filename = os.path.join(Path().resolve(), self.account_info_filename)
        file_exists = os.path.isfile(filename)
        if not file_exists:
            return
        with open(filename,'r',encoding="cp932" , newline='') as csv_file:
            f = csv.DictReader(csv_file, dialect='excel',delimiter=",", doublequote=True, lineterminator="\r\n", quotechar='"', skipinitialspace=True)
            for row in f:
                #print(row)
                account = row.get("account","")
                sub_account = row.get("sub_account","")
                item =  row.get("item","")
                side = row.get("side",None)
                method =  row.get("method",None)
                tax_cat =  row.get("tax_cat",None)
                disp_cat =  row.get("disp_cat",None)
                self.set_item_info(account,sub_account,item,side,method,tax_cat,disp_cat)

    def save(self,filename=None):
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), self.account_info_filename)
            filename = os.path.join(Path().resolve(), self.account_info_filename)

        with open(filename, 'w', newline='') as csv_file:
            fieldnames = ['account', 'sub_account','item','side','method','tax_cat','disp_cat']
            writer = csv.DictWriter(csv_file, fieldnames=fieldnames)
            writer.writeheader()
            for key,item_info in self.item_info.items():
                (account,sub_account,item) = key
                #print(account,sub_account,item)
                writer.writerow({'account':account, 'sub_account':sub_account,'item':item,'side':item_info.get("side",''),'method':item_info.get("method",''),'tax_cat':item_info.get("tax_cat",''),'disp_cat':item_info.get("disp_cat",'')})

class Ledger:
    def __init__(self,account,sub_account=None,item=None,records=None):
        #account is required.
            self.account = account
            self.sub_account = sub_account
            self.item = item
            self.records = records
            self.accInfo = AccountInfo()
    def get_all_in_quantity(self):
        #入庫数量の合計を返す  
        
        #side = get_default_side(self.account)
        side = self.accInfo.get_item_side(self.account,self.sub_account,self.item)
        
        if side =="Dr":
            quantity_records = [record["dr_quantity"] for record in self.records if (type(record["dr_quantity"]) is int) or (type(record["dr_quantity"]) is float)]
            return sum(quantity_records)
        if side =="Cr":
            quantity_records = [record["cr_quantity"] for record in self.records if (type(record["cr_quantity"]) is int) or (type(record["cr_quantity"]) is float)] 
            return sum(quantity_records)
                               
    def get_all_in_amount(self):
        #入庫金額の合計を返す   
        #side = get_default_side(self.account)
        side = self.accInfo.get_item_side(self.account,self.sub_account,self.item)
        if side =="Dr":
            amount_records = [record["dr_amount"] for record in self.records if (type(record["dr_amount"]) is int) or (type(record["dr_amount"]) is float)]
            return sum(amount_records)
        if side =="Cr":
            amount_records = [record["cr_amount"] for record in self.records if (type(record["cr_amount"]) is int) or (type(record["cr_amount"]) is float)]
            return sum(amount_records)
                             
    def get_last_in_quantity(self):
        #最後の入庫数量を返す
        #入庫がない場合はNoneを返す
        #side = get_default_side(self.account)
        side = self.accInfo.get_item_side(self.account,self.sub_account,self.item)
                              
        if side =="Dr":    
            quantity_records = [record["dr_quantity"] for record in self.records if (type(record["dr_quantity"]) is int) or (type(record["dr_quantity"]) is float)]
        if side =="Cr":
            quantity_records = [record["cr_quantity"] for record in self.records if (type(record["cr_quantity"]) is int) or (type(record["cr_quantity"]) is float)]  
        if len(quantity_records)>=1:
            return quantity_records[-1]
        else:
            return None
                                
    def get_last_in_amount(self):
        #最後の入庫金額を返す
        #入庫がない場合はNoneを返す
        #side = get_default_side(self.account)
        #print("get_last_in_amount")
        side = self.accInfo.get_item_side(self.account,self.sub_account,self.item)
        #print("side",side)
        if side =="Dr":    
            amount_records = [record["dr_amount"] for record in self.records if (type(record["dr_amount"]) is int) or (type(record["dr_amount"]) is float)]
        if side =="Cr":
            amount_records = [record["cr_amount"] for record in self.records if (type(record["cr_amount"]) is int) or (type(record["cr_amount"]) is float)]
        #print("amount_records",amount_records)
        if len(amount_records)>=1:
            return amount_records[-1]
        else:
            return None                             
        
    def get_all_out_quantity(self): 
        #side = get_default_side(self.account)
        side = self.accInfo.get_item_side(self.account,self.sub_account,self.item)
                              
        if side =="Dr":    
            quantity_records = [record["cr_quantity"] for record in self.records if (type(record["cr_quantity"]) is int) or (type(record["cr_quantity"]) is float)]
        if side =="Cr":
            quantity_records = [record["dr_quantity"] for record in self.records if (type(record["dr_quantity"]) is int) or (type(record["dr_quantity"]) is float)] 
        return sum(quantity_records)                      

    def get_out_price_lpc(self):
        #最終仕入原価法を使ったときの払出し価格を返す
        # 商品の仕入れがないときはNoneを返す

        all_in_amount = self.get_all_in_amount()
        all_in_quantity = self.get_all_in_quantity()
        #print("all_in_amount",all_in_amount)
        #print("all_in_quantity",all_in_quantity)
        if all_in_quantity==0:
            return None

        last_in_amount = self.get_last_in_amount()
        last_in_quantity = self.get_last_in_quantity()
        #print("last_in_amount",last_in_amount)
        #print("last_in_quantity",last_in_quantity)
        if last_in_quantity==0 or last_in_quantity==None:
            return None

        all_out_quantity = self.get_all_out_quantity()
        #print("all_out_quantity",all_out_quantity)
        
        stock_quantity = all_in_quantity - all_out_quantity
        stock_amount = stock_quantity*last_in_amount/last_in_quantity

        out_amount = all_in_amount-stock_amount
        out_quantity = all_in_quantity - stock_quantity

        if out_quantity==0:
            return None

        out_price = out_amount/out_quantity

        return out_price

    def get_out_price_pa(self):
        # 総平均法を使ったときの払い出し価格を返す
        # 商品の仕入れがないときはNoneを返す

        all_in_amount = self.get_all_in_amount()
        all_in_quantity = self.get_all_in_quantity()
        if all_in_quantity==0:
            return None
        
        out_price = all_in_amount/all_in_quantity
                                
        #all_out_quantity = self.get_all_out_quantity()

        #stock_quantity = all_in_quantity - all_out_quantity
        #if stock_quantity==0:
        #    return None
        #stock_amount = stock_quantity*all_in_amount/all_in_quantity

        #out_price = stock_amount/stock_quantity

        #out_amount = all_in_amount-stock_amount
        #out_quantity = all_in_quantity - stock_quantity
        #out_price = out_amount/out_quantity
        return out_price

class ItemQueueMA:
    # 移動平均法
    def __init__(self):
        self.quantity_amount={} ## key:(account,sub_account,item) value:(在庫数量,在庫金額)

    def put(self,account,sub_account,item,in_quantity,in_amount):
        #数量、金額として、0やマイナスも許容している
        if in_quantity is None:
            return
        if in_amount is None:
            return
        latest_quantity,latest_amouont = self.quantity_amount.get((account,sub_account,item),(None,None))
        if (latest_quantity is None) or (latest_amouont is None):
            latest_quantity = in_quantity
            latest_amouont = in_amount
        else:
            latest_quantity += in_quantity
            latest_amouont += in_amount
        self.quantity_amount[(account,sub_account,item)]=(latest_quantity,latest_amouont)

    def get(self,account,sub_account,item,out_quantity):
        # quantity: 取り出したい数量
        # 戻り値：（取り出した金額,取り出した数量）
        # 考え方　
        # 入っている数量が正の場合：取り出したい数量が入っている数量以下
        # 入っている数量が負の場合：取り出したい数量が入っている数量以上
        # の場合に、全て取り出すことができる

        latest_quantity,latest_amouont = self.quantity_amount.get((account,sub_account,item),(None,None))
        #登録がない場合には、 数量、金額ともにNoneを返す
        if (latest_quantity is None) or (latest_amouont is None):
            return (None,None)
        
        #取り出したい数量[quantity]が0の場合は、取り出した金額は0とする
        if out_quantity==0:
            return (0,0)
        
        #何も入っていない(数量が0の)場合には、 数量、金額ともに0を返す
        if latest_quantity == 0:
            return (0,0)
        
        if  0 <= latest_quantity < out_quantity:
            out_quantity = latest_quantity
            out_amount = latest_amouont
            self.quantity_amount[(account,sub_account,item)]=(0,0)
            return out_quantity,out_amount
        if  out_quantity < latest_quantity <= 0:
            out_quantity = latest_quantity
            out_amount = latest_amouont
            self.quantity_amount[(account,sub_account,item)]=(0,0)
            return out_quantity,out_amount        
        out_amount = latest_amouont / latest_quantity * out_quantity
        
        latest_quantity -= out_quantity
        latest_amouont -= out_amount
        
        self.quantity_amount[(account,sub_account,item)]=(latest_quantity,latest_amouont)
        
        return (out_quantity,out_amount)

    def get_all(self,account,sub_account,item):
        
        latest_quantity,latest_amouont = self.quantity_amount.get((account,sub_account,item),(None,None))
        #登録がない場合には、 数量、金額ともにNoneを返す
        if (latest_quantity is None) or (latest_amouont is None):
            return (None,None)
        
        out_quantity = latest_quantity
        out_amount = latest_amouont
        
        self.quantity_amount[(account,sub_account,item)]=(0,0)
        
        return out_quantity,out_amount
    
class ItemQueueFIFO:
    # 先入先出法
    def __init__(self):
        self.q={} ## key:(account,sub_account,item) value:queue which contains (quantity,amount)

    def put(self,account,sub_account,item,in_quantity,in_amount):
        #数量、金額として、0やマイナスも許容している
        if in_quantity is None:
            return
        if in_amount is None:
            return
        latest_q = self.q.get((account,sub_account,item),None)
        if latest_q is None:
            self.q[(account,sub_account,item)]=deque()
            self.q[(account,sub_account,item)].appendleft((in_quantity,in_amount))
        else:
            self.q[(account,sub_account,item)].appendleft((in_quantity,in_amount))

    def get(self,account,sub_account,item,quantity):
        # quantity: 取り出したい数量
        # 戻り値：（取り出した金額,取り出した数量）
        #古いものから取り出していく
        #取り出した数量合計の絶対値が、
        # 取り出したい数量[quantity]以上（取り出したい値が正の場合）または
        # 取り出したい数量[quantity]以下（取り出したい値が負の場合）となるまで取り出す
        #取り出したい数量[out_quantity]が0の場合は、取り出した金額は0とする
        #何も入っていない場合には、 数量、金額ともに0を返す
        #足りない場合には、実際に取り出し可能な数量、金額を返す
        
        #登録がない場合には、 数量、金額ともにNoneを返す
        latest_q = self.q.get((account,sub_account,item),None)
        if latest_q is None:
            return (None,None)
        
        #取り出したい数量[quantity]が0の場合は、取り出した金額は0とする
        if quantity==0:
            return 0,0
        
        #何も入っていない場合には、 数量、金額ともに0を返す
        if len(latest_q)==0:
            return (0,0)
        
        sum_out_quantity = 0
        sum_out_amount = 0
        while self.q[(account,sub_account,item)]:
            try:
                out_quantity,out_amount=self.q[(account,sub_account,item)].pop()
            except IndexError:
                return (sum_out_quantity,sum_out_amount)
            sum_out_quantity += out_quantity
            sum_out_amount += out_amount
            if  0 <= sum_out_quantity < quantity:
                continue
            if  quantity < sum_out_quantity <= 0:
                continue
            if  quantity==sum_out_quantity:
                return (sum_out_quantity,sum_out_amount)
            over_out_quantity = sum_out_quantity - quantity
            over_out_amount = out_amount/out_quantity*over_out_quantity
            self.q[(account,sub_account,item)].append((over_out_quantity,over_out_amount))
            sum_out_quantity -= over_out_quantity
            sum_out_amount -=over_out_amount
            return (sum_out_quantity,sum_out_amount)
        
    def get_all(self,account,sub_account,item):
        #登録がない場合には、 数量、金額ともにNoneを返す
        latest_q = self.q.get((account,sub_account,item),None)
        if latest_q is None:
            return (None,None)
        sum_out_quantity = 0
        sum_out_amount = 0
        while self.q[(account,sub_account,item)]:
            try:
                out_quantity,out_amount=self.q[(account,sub_account,item)].pop()
            except IndexError:
                return (sum_out_quantity,sum_out_amount)
            sum_out_quantity += out_quantity
            sum_out_amount += out_amount
        return (sum_out_quantity,sum_out_amount)

class Ledgers:
    def __init__(self):
        #self.memo_dict ={}
        #self.gb ={"partner":None,"item":None,"person_in_charge":None,"memo":{}}
        #抽出条件をどのように指定するか
        #
        #sub_accountごとに、顧客・担当者・itemの３軸＋メモで修飾されている
        #その場合、期首残高をどのように表現するか
        #
        #TBのデータ形式
        #
        #class Ledgers
        # start_date:<datetime>
        # end_date:<datetime>
        # records:[<record>,<record>,....]
        #<record>
        # 期首残高は、memo　key:KIND　value:OPENINGを指定して表現  &KIND::OPENING
        # 決算整理は、mono key:KIND　value:ADJUSTINGを指定して表現  &KIND::ADJUSTING
        # remarksは仕訳のremarks と各勘定のremarks を連結したもの
        # datetime :<datetime>
        # account
        # sub_account
        # item
        # partner
        # person_in_charge
        # memo:[]
        # remarks
        # quantity_unit
        # amount_unit          
        # dr_quantity
        # dr_amount
        # cr_quantity
        # cr_amount
       
        self.start_date=None
        self.end_date=None
        self.records=[]
        self.global_header = {}
        self.accInfo = AccountInfo()
        
        #fieldnames=["id","entry_id","kind","datetime","account","sub_account","借方担当者","借方税区分","借方金額","借方税額","借方金額単位","借方数量","借方数量単位","借方取引先","借方品目","借方メモ","借方摘要","貸方勘定科目","貸方補助科目","貸方部門","貸方担当者","貸方税区分","貸方金額","貸方税額","貸方金額単位","貸方数量","貸方数量単位","貸方取引先","貸方品目","貸方メモ","貸方摘要","摘要"]
        #self.records = pd.DataFrame(index=[],columns=fieldnames)
        # item、取引先、担当者、memo のスコープ  
        # １　debit/credit:debit 又は　credit　内で指定した場合
        # ２　journal_entry:　debit/creditが含まれるjournal_entryのheaderで指定した場合
        # ３　journal:debit/creditが含まれないjournal_entryのheaderで指定した場合（変更されるまでその値を保持）
        # 同じitem 取引先　memoのキー　が指定されている場合の優先順位　１＞２＞３　で上書きして適用

    def get_record_df(self):
        #レコードのデータをdataframeとして取得
        #分析用
        #<record>
        # 期首残高は、memo　key:KIND　value:OPENINGを指定して表現   &KIND::OPENING
        # 決算整理は、mono key:KIND　value:ADJUSTINGを指定して表現  &KIND::ADJUSTING
        # remarksは仕訳のremarks と各勘定のremarks を連結したもの
        # datetime :<datetime>
        # account
        # sub_account
        # item
        # partner
        # person_in_charge
        # memo:[]
        # remarks
        # quantity_unit
        # amount_unit          
        # dr_quantity
        # dr_amount
        # cr_quantity
        # cr_amount
        key_list = ["entry_id","counts_dr_cr","order_id","line_no","datetime","account","sub_account","item","partner","person_in_charge","memo","memo_str","memo_number","memo_number_unit","price","quantity","quantity_unit","amount","amount_unit","dr_quantity","dr_amount","cr_quantity","cr_amount","remarks"]
        rec_df = pd.DataFrame.from_records(self.records,columns=key_list)
        #df_memo = df['memo'].apply(lambda x: pd.Series(literal_eval(x)))

        rec_df['memo_str']=rec_df['memo_str'].astype(str)
        df_memo_str = rec_df['memo_str'].apply(lambda x: pd.Series(x,dtype=object))
        df_memo_str = df_memo_str[0].apply(lambda x: pd.Series(literal_eval(x),dtype=object))

        rec_df['memo_number']=rec_df['memo_number'].astype(str)
        df_memo_number = rec_df['memo_number'].apply(lambda x: pd.Series(x,dtype=object))
        df_memo_number = df_memo_number[0].apply(lambda x: pd.Series(literal_eval(x),dtype=object))

        rec_df = rec_df.join(df_memo_str,how="outer")
        rec_df = rec_df.join(df_memo_number,how="outer")
        
        return rec_df
    
    def get_records(self,account,sub_account=None,item=None):
        #sub_account がNoneのときは総勘定元帳に相当するrecordを返す
        #itemがNoneのときは補助元帳に相当するrecordを返す
        
        if account is None:
            return None
        if sub_account is None:
            records = [record for record in self.records if record["account"]==account]
        else:
            if item is None:
                records = [record for record in self.records if record["account"]==account and record["sub_account"]==sub_account]
            else:
                records = [record for record in self.records if record["account"]==account and record["sub_account"]==sub_account and record["item"]==item]
        return records
    
    def get_ledger(self,account,sub_account=None,item=None):
        #sub_account がNoneのときは総勘定元帳を返す
        #itemがNoneのときは補助元帳を返す        
        records = self.get_records(account,sub_account,item)
        if records is None:
            return None
        return Ledger(account,sub_account,item,records)

    def simple_ledger_to_df(self,account,sub_account=None,item=None):
        #records
        records = self.get_records(account,sub_account,item)
        if records is None:
            return None

        #DataFrame
        if item is None:
            key_list = ["entry_id","datetime","amount","amount_unit","dr_amount","cr_amount","remarks"]
        else:
            key_list = ["entry_id","datetime","quantity","quantity_unit","amount","amount_unit","dr_quantity","dr_amount","cr_quantity","cr_amount","remarks"]
        
        #out_df = pd.DataFrame(columns=key_list)
        out_df = pd.DataFrame.from_records(records,columns=key_list)
        
        return out_df
    
    def simple_ledger_to_excel(self,account,sub_account=None,item=None,filename=None):

        out_df = self.simple_ledger_to_df(account,sub_account,item)
        if out_df is None:
            return
        #filename
        basename = account
        if sub_account is not None:
            basename += "_"+sub_account
        if item is not None:
            basename += "_"+item
            
        method = self.accInfo.get_item_method(account,sub_account,item)
        #side = self.accInfo.get_item_side(account,sub_account,item)
        
        if method is not None:
                basename += "_"+method
        basename_and_ext = basename +".xlsx"

        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), basename)
            filename = os.path.join(Path().resolve(), basename_and_ext)

        #sheet_name
        sheet_name = basename
        
        #out_df["取引日付"]=out_df["取引日付"].dt.strftime('%Y/%m/%d')
        with pd.ExcelWriter(filename) as writer:  
            out_df.to_excel(writer, sheet_name=sheet_name,index_label=basename)

    def tb_partner_vs_end_to_df(self,start_datetime=None,end_datetime=None):
        tb_partners = self.get_tb_with_partner(start_datetime,end_datetime)
        #partners = tb_partners.keys()
        #df = pd.DataFrame(columns=partners)
        mindex = pd.MultiIndex.from_tuples([],names=('disp_cat','account', 'sub_account','item'))
        df = pd.DataFrame(index=mindex)
        for partner,tb in tb_partners.items():
            #(表示カテゴリ、account,sub_account_item)をdfのインデックスにする
            keys = [(self.accInfo.get_item_disp_cat(*key),key[0],key[1],key[2]) for key in tb.keys()]
            index = pd.MultiIndex.from_tuples(keys,names=('disp_cat','account', 'sub_account','item'))
            if partner is None:
                partner="OTHERS"
            columns = [partner+"_end_quanitiy",partner+"_end_amount"]
            q_data = [v.get("end_quantity",None) for v in tb.values()]
            a_data = [v.get("end_amount",None) for v in tb.values()]
            data = zip(q_data,a_data)
            df2 = pd.DataFrame(data,index=index,columns=columns)
            df = pd.merge(df, df2, on = ('disp_cat','account', 'sub_account','item'),how='outer')
        df = df.sort_index()
        return df
    
    def tb_partner_vs_end_to_excel(self,filename=None,start_datetime=None,end_datetime=None):
        #filename
        basename ="TB_partner_vs_end"
        basename_and_ext = basename +".xlsx"
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), basename)
            filename = os.path.join(Path().resolve(), basename_and_ext)
            
        #sheet_name
        sheet_name = basename
        
        out_df = self.tb_partner_vs_end_to_df(start_datetime,end_datetime)
        with pd.ExcelWriter(filename) as writer:  
            out_df.to_excel(writer, sheet_name=sheet_name,index_label=basename)            

    def tb_person_in_charge_vs_end_to_df(self,start_datetime=None,end_datetime=None):
        tb_person_in_charges = self.get_tb_with_person_in_charge(start_datetime,end_datetime)
        #person_in_charges = tb_person_in_charges.keys()
        #df = pd.DataFrame(columns=person_in_charges)
        mindex = pd.MultiIndex.from_tuples([],names=('disp_cat','account', 'sub_account','item'))
        df = pd.DataFrame(index=mindex)
        for person_in_charge,tb in tb_person_in_charges.items():
            #(表示カテゴリ、account,sub_account_item)をdfのインデックスにする
            keys = [(self.accInfo.get_item_disp_cat(*key),key[0],key[1],key[2]) for key in tb.keys()]
            index = pd.MultiIndex.from_tuples(keys,names=('disp_cat','account', 'sub_account','item'))
            if person_in_charge is None:
                person_in_charge="OTHERS"
            columns = [person_in_charge+"_end_quanitiy",person_in_charge+"_end_amount"]
            q_data = [v.get("end_quantity",None) for v in tb.values()]
            a_data = [v.get("end_amount",None) for v in tb.values()]
            data = zip(q_data,a_data)
            df2 = pd.DataFrame(data,index=index,columns=columns)
            df = pd.merge(df, df2, on = ('disp_cat','account', 'sub_account','item'),how='outer')
        df = df.sort_index()
        return df

    def tb_person_in_charge_vs_end_to_excel(self,filename=None,start_datetime=None,end_datetime=None):
        #filename
        basename ="TB_person_in_charge_vs_end"
        basename_and_ext = basename +".xlsx"
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), basename)
            filename = os.path.join(Path().resolve(), basename_and_ext)
            
        #sheet_name
        sheet_name = basename
        
        out_df = self.tb_person_in_charge_vs_end_to_df(start_datetime,end_datetime)
        with pd.ExcelWriter(filename) as writer:  
            out_df.to_excel(writer, sheet_name=sheet_name,index_label=basename)            

    def tb_memo_vs_end_to_df(self,memo_key,start_datetime=None,end_datetime=None):
        tb_memos = self.get_tb_with_memo(memo_key,start_datetime,end_datetime)
        #memos = tb_memos.keys()
        #df = pd.DataFrame(columns=memos)
        mindex = pd.MultiIndex.from_tuples([],names=('disp_cat','account', 'sub_account','item'))
        df = pd.DataFrame(index=mindex)
        for memo,tb in tb_memos.items():
            #(表示カテゴリ、account,sub_account_item)をdfのインデックスにする
            keys = [(self.accInfo.get_item_disp_cat(*key),key[0],key[1],key[2]) for key in tb.keys()]
            index = pd.MultiIndex.from_tuples(keys,names=('disp_cat','account', 'sub_account','item'))
            if memo is None:
                memo="OTHERS"
            columns = [memo+"_end_quanitiy",memo+"_end_amount"]
            q_data = [v.get("end_quantity",None) for v in tb.values()]
            a_data = [v.get("end_amount",None) for v in tb.values()]
            data = zip(q_data,a_data)
            df2 = pd.DataFrame(data,index=index,columns=columns)
            df = pd.merge(df, df2, on = ('disp_cat','account', 'sub_account','item'),how='outer')
        df = df.sort_index()
        return df

    def tb_memo_vs_end_to_excel(self,memo_key,filename=None,start_datetime=None,end_datetime=None):
        #filename
        basename ="TB_memo_vs_end"+"_"+memo_key
        basename_and_ext = basename +".xlsx"
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), basename)
            filename = os.path.join(Path().resolve(), basename_and_ext)
            
        #sheet_name
        sheet_name = basename
        
        out_df = self.tb_memo_vs_end_to_df(memo_key,start_datetime,end_datetime)
        with pd.ExcelWriter(filename) as writer:  
            out_df.to_excel(writer, sheet_name=sheet_name,index_label=basename)            

    def tb_to_df(self,start_datetime=None,end_datetime=None,rec_cond_func=None):
        #tb_dics
        tb = self.get_tb(start_datetime,end_datetime,rec_cond_func)
        
        tb_dics = [{**{"account":k[0],"sub_account":k[1],"item":k[2]},**v} for k,v in tb.items()]
                
        #DataFrame
        #key_list = ["account","sub_account","item","opening_quantity","opening_amount","sum_dr_quantity","sum_dr_amount","sum_cr_quantity","sum_cr_amount","end_quantity","end_amount"]
        key_list = ["account","sub_account","item","start_quantity","start_amount","sum_dr_quantity","sum_dr_amount","sum_cr_quantity","sum_cr_amount","end_quantity","end_amount"]

        out_df = pd.DataFrame.from_records(tb_dics,columns=key_list)

        return out_df
    
    def tb_to_excel(self,filename=None,start_datetime=None,end_datetime=None,rec_cond_func=None):

        out_df = self.tb_to_df(start_datetime,end_datetime,rec_cond_func)
        
        #filename
        basename ="TB"
        basename_and_ext = basename +".xlsx"
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), basename)
            filename = os.path.join(Path().resolve(), basename_and_ext)
            
        #sheet_name
        sheet_name = basename
        
        print("filename",filename)
        with pd.ExcelWriter(filename) as writer:  
            out_df.to_excel(writer, sheet_name=sheet_name,index_label=basename)            
    
    
    # memo:[]
    
    def get_partner_list(self):
        partners =set()
        for record in self.records:
            partner = record.get("partner",None)
            if partner is not None:
                partners.add(partner)
        partners_lst = sorted(list(partners))
        return partners_lst

    def get_person_in_charge_list(self):
        person_in_charges =set()
        for record in self.records:
            person_in_charge = record.get("person_in_charge",None)
            if person_in_charge is not None:
                person_in_charges.add(person_in_charge)
        person_in_charges_lst = sorted(list(person_in_charges))
        return person_in_charges_lst
    
    def get_memo_list(self,memo_key):
        values = set()
        for record in self.records:
            memo = record.get("memo",None)
            if memo is not None:
                value = memo.get(memo_key,None)
                if value is not None:
                    if type(value) is str:
                        values.add(value)
        values_lst = sorted(list(values))
        return values_lst
    
    def get_tb_with_partner(self,start_datetime=None,end_datetime=None):
        partners = self.get_partner_list()
        partners.append(None)
        tb_with_partner={}
        
        for partner in partners:
            rec_cond_func = lambda rec: rec.get("partner",None)==partner
            tb = self.get_tb(start_datetime,end_datetime,rec_cond_func)
            tb_with_partner[partner]=tb
        return tb_with_partner

    def get_tb_with_person_in_charge(self,start_datetime=None,end_datetime=None):
        pics = self.get_person_in_charge_list()
        pics.append(None)
        tb_with_pic={}
        
        for pic in pics:
            rec_cond_func = lambda rec: rec.get("person_in_charge",None)==pic
            tb = self.get_tb(start_datetime,end_datetime,rec_cond_func)
            tb_with_pic[pic]=tb
        return tb_with_pic
    
    def get_tb_with_memo(self,memo_key,start_datetime=None,end_datetime=None):
        memos = self.get_memo_list(memo_key)
        memos.append(None)
        tb_with_memo={}
        
        for memo in memos:
            rec_cond_func = lambda rec: (rec.get("memo",None) is not None) and (rec["memo"].get(memo_key,None) == memo)
            tb = self.get_tb(start_datetime,end_datetime,rec_cond_func)
            tb_with_memo[memo]=tb
        return tb_with_memo
    
    def get_tb(self,start_datetime=None,end_datetime=None,rec_cond_func=None):
        tb = {}       
        # start_datetime <= 仕訳の日付　< end_datetime
        # を集計
        # end_datetimeは集計範囲に含まれないので注意
        # start_datetime end_datetime は、ISO 8601 format　の文字列
        # rec_cond_func recordを引数とする関数  recordを集計対象とする場合True 集計対象としない場合False を返す関数
        # opening_*** 繰越
        # before_start_*** 集計期間より前
        # sum_dr_quantity sum_dr_amount sum_cr_quantity sum_cr_amount 集計期間中
        if start_datetime is not None:
            dt_start_datetime = datetime.datetime.fromisoformat(start_datetime)
        else:
            dt_start_datetime  = None
            
        if end_datetime is not None:    
            dt_end_datetime = datetime.datetime.fromisoformat(end_datetime)
        else:
            dt_end_datetime  = None
            
        for record in self.records:
            if rec_cond_func is not None:
                if not rec_cond_func(record):
                    continue
            account = record.get("account",None)
            if account is None:
                continue
            #sub_accountは指定されている必要がある
            #sub_accountを指定しない場合は{"sub_account":""}としておく
            sub_account = record.get("sub_account",None)
            if sub_account is None:
                continue
            #itemは指定されている必要がある
            #itemを指定しない場合は{"item":""}としておく                
            item = record.get("item",None)
            if item is None:
                continue

            date_or_datetime = record.get("datetime",None)
            if date_or_datetime is None:
                continue
            dt_datetime_rec = datetime.datetime.fromisoformat(date_or_datetime)
            
            
            # 期首残高は、memo　key:KIND　value:OPENINGを指定して表現  &KIND::OPENING
            # 決算整理は、meno key:KIND　value:ADJUSTINGを指定して表現  &KIND::ADJUSTING                
            memo = record.get("memo",None)
            #開始仕訳
            opening=False
            if "KIND" in memo and memo["KIND"]=="OPENING":
                opening= True
            adjusting=False
            #決算整理仕訳
            if "KIND" in memo and memo["KIND"]=="ADJUSTING":
                adjusting= True
            
            #はじめての項目の場合
            key = (account,sub_account,item)
            if key not in tb:
                tb.update({key:{"opening_quantity":0,"opening_amount":0,"before_start_sum_dr_quantity":0,"before_start_sum_dr_amount":0,"before_start_sum_cr_quantity":0,"before_start_sum_cr_amount":0,"sum_dr_quantity":0,"sum_dr_amount":0,"sum_cr_quantity":0,"sum_cr_amount":0}})
            
            #side
            side = self.accInfo.get_item_side(account,sub_account,item)
            
            #dr_quantityの集計
            dr_quantity = record.get("dr_quantity",None)
            #None（記載なし）は集計しない
            if (type(dr_quantity) is int) or (type(dr_quantity) is float):
                #開始仕訳の集計
                if opening:
                    if side == "Dr":
                        tb[key]["opening_quantity"] += dr_quantity
                    if side == "Cr":
                        tb[key]["opening_quantity"] -= dr_quantity                
                elif (start_datetime is not None) and (dt_datetime_rec<dt_start_datetime):
                        tb[key]["before_start_sum_dr_quantity"] += dr_quantity   
                elif (end_datetime is None) or (dt_datetime_rec<dt_end_datetime):
                        tb[key]["sum_dr_quantity"] += dr_quantity                     
                else:
                    pass
                
            #dr_amountの集計
            dr_amount = record.get("dr_amount",None)
            #None（記載なし）は集計しない
            if (type(dr_amount) is int) or (type(dr_amount) is float):
                #開始仕訳の集計
                if opening:
                    if side == "Dr":
                        tb[key]["opening_amount"] += dr_amount
                    if side == "Cr":
                        tb[key]["opening_amount"] -= dr_amount                
                elif (start_datetime is not None) and (dt_datetime_rec<dt_start_datetime):
                        tb[key]["before_start_sum_dr_amount"] += dr_amount
                elif (end_datetime is None) or (dt_datetime_rec<dt_end_datetime):
                        tb[key]["sum_dr_amount"] += dr_amount   
                else:
                    pass
                
            #cr_quantityの集計
            cr_quantity = record.get("cr_quantity",None)
            #None（記載なし）は集計しない
            if (type(cr_quantity) is int) or (type(cr_quantity) is float):
                #開始仕訳の集計
                if opening:
                    if side == "Dr":
                        tb[key]["opening_quantity"] -= cr_quantity
                    if side == "Cr":
                        tb[key]["opening_quantity"] += cr_quantity
                elif (start_datetime is not None) and (dt_datetime_rec<dt_start_datetime):
                        tb[key]["before_start_sum_cr_quantity"] += cr_quantity   
                elif (end_datetime is None) or (dt_datetime_rec<dt_end_datetime):
                        tb[key]["sum_cr_quantity"] += cr_quantity                     
                else:
                    pass
                
            #cr_amountの集計
            cr_amount = record.get("cr_amount",None)
            #None（記載なし）は集計しない
            if (type(cr_amount) is int) or (type(cr_amount) is float):
                #開始仕訳の集計
                if opening:
                    if side == "Dr":
                        tb[key]["opening_amount"] -= cr_amount
                    if side == "Cr":
                        tb[key]["opening_amount"] += cr_amount                
                elif (start_datetime is not None) and (dt_datetime_rec<dt_start_datetime):
                        tb[key]["before_start_sum_cr_amount"] += cr_amount
                elif (end_datetime is None) or (dt_datetime_rec<dt_end_datetime):
                        tb[key]["sum_cr_amount"] += cr_amount  
  
            if side == "Dr":
                tb[key]["start_quantity"]=tb[key]["opening_quantity"]+tb[key]["before_start_sum_dr_quantity"]-tb[key]["before_start_sum_cr_quantity"]
                tb[key]["start_amount"]=tb[key]["opening_amount"]+tb[key]["before_start_sum_dr_amount"]-tb[key]["before_start_sum_cr_amount"]        
                tb[key]["end_quantity"]=tb[key]["start_quantity"]+tb[key]["sum_dr_quantity"]-tb[key]["sum_cr_quantity"]
                tb[key]["end_amount"]=tb[key]["start_amount"]+tb[key]["sum_dr_amount"]-tb[key]["sum_cr_amount"]
            elif side == "Cr":
                tb[key]["start_quantity"]=tb[key]["opening_quantity"]+tb[key]["before_start_sum_cr_quantity"]-tb[key]["before_start_sum_dr_quantity"]
                tb[key]["start_amount"]=tb[key]["opening_amount"]+tb[key]["before_start_sum_cr_amount"]-tb[key]["before_start_sum_dr_amount"]
                tb[key]["end_quantity"]=tb[key]["start_quantity"]+tb[key]["sum_cr_quantity"]-tb[key]["sum_dr_quantity"]
                tb[key]["end_amount"]=tb[key]["start_amount"]+tb[key]["sum_cr_amount"]-tb[key]["sum_dr_amount"]
        
        #sort 表示カテゴリ順にソート
        tb_lst = sorted(tb.items(),key = lambda x:self.accInfo.get_item_disp_cat(*x[0]))
        tb = dict((x, y) for x, y in tb_lst)
        
        #return tb_lst
        return tb

    def calc_op_equal_quantity(self,journal_entry):
        # OP_EQUAL_QUANTITY
        # journal_entry を書き換ええるので注意
        if "debit" in  journal_entry:
            for (d_index,d) in enumerate(journal_entry["debit"]):
                quantity = d.get("quantity",None)
                if quantity == 'OP_EQUAL_QUANTITY':
                    if "credit" not in  journal_entry:
                        # 相手科目がない場合は0
                        journal_entry["debit"][d_index]["quantity"]=0
                    if len(journal_entry["credit"])<=d_index:
                        journal_entry["debit"][d_index]["quantity"]=0
                    equal_value = journal_entry["credit"][d_index].get("quantity",None)
                    journal_entry["debit"][d_index]["quantity"]=equal_value

        if "credit" in  journal_entry:
            for (c_index,c) in enumerate(journal_entry["credit"]):
                quantity = c.get("quantity",None)
                if quantity == 'OP_EQUAL_QUANTITY':
                    if "debit" not in  journal_entry:
                        # 相手科目がない場合は0
                        journal_entry["credit"][c_index]["quantity"]=0
                    if len(journal_entry["debit"])<=c_index:
                        journal_entry["credit"][c_index]["quantity"]=0
                    equal_value = journal_entry["debit"][c_index].get("quantity",None)
                    journal_entry["credit"][c_index]["quantity"]=equal_value
                    
        return journal_entry

    def calc_sum_quantity(self,journal_entry):
        sum_quantity_debit = 0
        sum_quantity_credit = 0
        if "debit" in  journal_entry:
            for d in journal_entry["debit"]:
                quantity = d.get("quantity",None)
                if (type(quantity) is int) or (type(quantity) is float):
                    sum_quantity_debit += quantity

        if "credit" in  journal_entry:
            for c in journal_entry["credit"]:
                quantity = c.get("quantity",None)
                if (type(quantity) is int) or (type(quantity) is float):
                    sum_quantity_credit += quantity
        
        return (sum_quantity_debit,sum_quantity_credit)
    
    def calc_op_diff_quantity(self,journal_entry):
        # OP_DIFF_QUANTITY
        # only one diff_quantity is allowed in the journal_entry.
        # If more than one diff_quantitys are in the journal_entry, those value will be 0.
        # journal_entry を書き換ええるので注意

        before_filled = True
        sum_quantity_debit,sum_quantity_credit = self.calc_sum_quantity(journal_entry)
        
        if "debit" in  journal_entry:
            for (d_index,d) in enumerate(journal_entry["debit"]):
                quantity = d.get("quantity",None)
                if quantity == 'OP_DIFF_QUANTITY':
                    if before_filled:
                        journal_entry["debit"][d_index]["quantity"]=sum_quantity_credit - sum_quantity_debit
                        before_filled = False
                    else:
                        journal_entry["debit"][d_index]["quantity"]=0
                    
        if "credit" in  journal_entry:
            for (c_index,c) in enumerate(journal_entry["credit"]):
                quantity = c.get("quantity",None)
                if quantity == 'OP_DIFF_QUANTITY':
                    if before_filled:
                        journal_entry["credit"][c_index]["quantity"]= sum_quantity_debit - sum_quantity_credit
                        b_filled = True
                    else:
                        journal_entry["credit"][c_index]["quantity"]==0
        
        return journal_entry

    def calc_sum_amount(self,journal_entry):
        sum_amount_debit = 0
        sum_amount_credit = 0
        if "debit" in  journal_entry:
            for d in journal_entry["debit"]:
                amount = d.get("amount",None)
                if (type(amount) is int) or (type(amount) is float):
                    sum_amount_debit += amount

        if "credit" in  journal_entry:
            for c in journal_entry["credit"]:
                amount = c.get("amount",None)
                if (type(amount) is int) or (type(amount) is float):
                    sum_amount_credit += amount

        return (sum_amount_debit,sum_amount_credit)
        
    
    #def calc_op_amount(self,journal_entry):
    #op_amount: OP_AUTO_AMOUNT | OP_BALANCE_AMOUNT | OP_DIFF_AMOUNT | OP_EQUAL_AMOUNT
    #    journal_entry = self.calc_op_balance_amount(journal_entry)
    #    journal_entry = self.calc_op_equal_amount(journal_entry)
    #    journal_entry = self.calc_op_diff_amount(journal_entry)
    #    journal_entry = self.calc_op_auto_amount(journal_entry)
    #    return journal_entry
    
    def resigter_datetime(self,journal_entry):
        journal_entry_datetime = journal_entry["entry_header"]["datetime"]
        if self.start_date is None:
            self.start_date=journal_entry_datetime

        if self.end_date is None:
            self.end_date=journal_entry_datetime  

        if  journal_entry_datetime < self.start_date:
            self.start_date=journal_entry_datetime

        if  self.end_date < journal_entry_datetime:
            self.end_date=journal_entry_datetime
    
    def addInfo(self,journal_entry):
        # journal_entry を書き換ええるので注意
        
        entry_header = journal_entry.get("entry_header",None)
        if entry_header is None:
            raise ValueError('Entry_header must be specified.')
        debit =journal_entry.get("debit",[])
        credit =journal_entry.get("credit",[])
        #counts_dr_cr
        counts_dr_cr = len(debit)+len(credit)
        journal_entry["entry_header"]["counts_dr_cr"]=counts_dr_cr
        return journal_entry
        
    def register(self,journal_entry):
        self.resigter_datetime(journal_entry)
        #journal_entry = self.calc_op_quantity(journal_entry) 
        journal_entry = self.addInfo(journal_entry)
        #OP_EQUAL_QUANTITY
        journal_entry = self.calc_op_equal_quantity(journal_entry)
        #OP_DIFF_QUANTITY
        journal_entry = self.calc_op_diff_quantity(journal_entry)
        #journal_entry = self.calc_op_amount(journal_entry)    
        #self.register_raw_quantity(journal_entry)
        entry_header = journal_entry.get("entry_header",None)
        if entry_header is None:
            raise ValueError('Entry_header must be specified.')
        debit =journal_entry.get("debit",[])
        credit =journal_entry.get("credit",[])
        
        #debit　および　credit　が指定されていないentry_headerの場合は、global_headerを書き換える
        if len(debit)==0 and len(credit)==0:
            self.global_header = {**self.global_header,**entry_header}
            return
        
        for d,c in zip_longest(debit,credit):
            self.fill_dr(entry_header,d)
            self.fill_cr(entry_header,c)        
            
    def mearge_dic(self,original_dic,new_dic):
        original_dic_memo = original_dic.get("memo",{})
        original_dic_remarks = original_dic.get("remarks","")
        #partner,person_in_charge overridden if key exists
        mearged_dic = {**original_dic,**new_dic}
        if "memo" in mearged_dic:
            mearged_dic["memo"] = {**original_dic_memo,**mearged_dic["memo"]}
        else:
            mearged_dic["memo"] = {**original_dic_memo}
        if "remarks" in mearged_dic:
            mearged_dic["remarks"] = mearged_dic["remarks"]+original_dic_remarks
        else:
            mearged_dic["remarks"] = original_dic_remarks
        return mearged_dic
    
    def fill_qa(self,dic,side):
        #辞書を書き換えるので注意
        #sub_accountが指定されていない場合は{"sub_account":""}を追加
        #itemが指定されていない場合は{"item":""}を追加
        
        if side =="Dr":
            fillside_amount = "dr_amount"
            oppside_amount ="cr_amount"
            fillside_quantity = "dr_quantity"
            oppside_quantity ="cr_quantity"
        elif side =="Cr":
            fillside_amount = "cr_amount"
            oppside_amount ="dr_amount"
            fillside_quantity = "cr_quantity"
            oppside_quantity ="dr_quantity"            
        else:
            pass
        
        dic[fillside_quantity]= dic.get("quantity",None)
        dic[fillside_amount]= dic.get("amount",None)
        dic[oppside_quantity]= None
        dic[oppside_amount]= None
        
        if "item" not in dic:
            dic["item"] = "" #not specified
        if "sub_account" not in dic:
            dic["sub_account"]="" #not specified
        
        if "amount" not in dic:
            #you must specify quantity and price
            if "quantity" in dic:
                quantity = dic["quantity"]
                if (type(quantity) is int) or (type(quantity) is float):
                    if "price" in dic:
                        price = dic["price"]
                        if (type(price) is int) or (type(price) is float):
                            dic[fillside_amount] = price * quantity
                        else:
                            raise ValueError('fill_dr:price must be float or int and none zero.')
                    else:
                        #price not spesicied
                        raise ValueError('fill_dr:only quantity specified.')
                else:
                    #quantity is operator caliculated later.
                    if "price" not in dic:
                        raise ValueError('fill_dr:you must specify price or amount.')
            else:
                #amount and quantity not specified
                raise ValueError('fill_dr:amount and quantity not specified.')
        
        #amount is spesicied
        #amount = dic["amount"]
        amount = dic[fillside_amount]
        if (type(amount) is int) or (type(amount) is float):
            # amount is number
            if "quantity" in dic:
                #amount and quantity is specified
                pass
            else:
                if "price" in dic:
                    price = dic["price"]
                    if (type(price) is int) or (type(price) is float) and price !=0:
                        dic[fillside_quantity] = amount / price
                    else:
                        raise ValueError('fill_dr:price must be float or int and none zero.')
                else:
                    dic[fillside_quantity] = 1 #価額のみの指定の場合、数量は１
        else:
            #amount is operstor caliculated later.
            if "quantity" in dic:
                #amount and quantity specifed.
                pass
            else:
                if "price" in dic:
                    #amount and price is specified
                    pass
                else:
                    dic[fillside_quantity] = 1 #価額のみの指定の場合、数量は１
                    
        #print("dic",dic)
        return dic
    
    def fill_dr(self,entry_header,d):
        if entry_header is None:
            return
        if d is None:
            return
        
        d2 = self.mearge_dic(entry_header,d)
        d3 = self.mearge_dic(self.global_header,d2)
        #header_memo = entry_header.get("memo",{})
        #header_remarks = entry_header.get("remarks","")
        #partner,person_in_charge overridden by d if key exists
        #dd = {**entry_header,**d}
        #dd["memo"] = {**header_memo,**dd["memo"]}
        #dd["remarks"] = dd["remarks"]+header_remarks
        
        
         #d4 = self.recalc(d3)
        d4 = self.fill_qa(d3,"Dr")
        d5 = self.add_memo_type(d4)
        #print("d4",d4)
        self.records.append(d5)

    def add_memo_type(self,dic):
        #dic　を書き換えるので注意
        memo = dic.get("memo",None)
        if memo is None:
            dic["memo"]={}
        memo_str = dic.get("memo_str",None)
        if memo_str is None:
            dic["memo_str"]={}
        memo_number = dic.get("memo_number",None)
        if memo_number is None:
            dic["memo_number"]={}
        for k,v in memo.items():
            if type(v) is str:
                if "memo_str" not in dic:
                    dic["memo_str"]={k:v}
                else:
                    dic["memo_str"].update({k:v})
            elif type(v) is tuple:
                if "memo_number" not in dic:
                    dic["memo_number"]={k:v[0]}
                else:
                    dic["memo_number"].update({k:v[0]})
                if "memo_number_unit" not in dic:
                    dic["memo_number_unit"]={k:v[1]}
                else:
                    dic["memo_number_unit"].update({k:v[1]})                    
        return dic
    
    def fill_cr(self,entry_header,c):
        if entry_header is None:
            return
        if c is None:
            return
        
        c2 = self.mearge_dic(entry_header,c)
        c3 = self.mearge_dic(self.global_header,c2)
        
        c4 = self.fill_qa(c3,"Cr")
        c5 = self.add_memo_type(c4)
        self.records.append(c5)
    
    def get_balance_quantity(self,idx,side="Dr"):
        dr_quantity = [record["dr_quantity"] for record in self.records[:idx]]
        sum_dr_quantity = sum(dr_quantity)
        cr_quantity = [record["cr_quantity"] for record in self.records[:idx]]
        sum_cr_quantity = sum(cr_quantity)        
        if side=="Dr":
            return sum_dr_quantity - sum_cr_quantity
        if side=="Cr":
            return sum_cr_quantity - sum_dr_quantity
        
        raise ValueError('get_balance_quantity:side must be Dr or Cr.')
        return None

    def get_balance_amount(self,idx,side="Dr"):
        dr_amount = [record["dr_amount"] for record in self.records[:idx]]
        sum_dr_amount = sum(dr_amount)
        cr_amount = [record["cr_amount"] for record in self.records[:idx]]
        sum_cr_amount = sum(cr_amount)        
        if side=="Dr":
            return sum_dr_amount - sum_cr_amount
        if side=="Cr":
            return sum_cr_amount - sum_dr_amount
        
        raise ValueError('get_balance_amount:side must be Dr or Cr.')
        return None
    

    def get_out_price_lpc(self,account,sub_account,item):
        #最終仕入原価法を使ったときの払出し価格を返す
        # 商品の仕入れがないときはNoneを返す
        #print("get_out_price_lpc")
        #print("account",account,"sub_account",sub_account,"item",item)
        #print("self.records",self.records)
        
        ledger = self.get_ledger(account,sub_account,item)
        #print("ledger.records",ledger.records)
        if ledger is None:
            return None
        
        out_price = ledger.get_out_price_lpc()
        
        return out_price
    
    def get_out_price_pa(self,account,sub_account,item):
        ledger = self.get_ledger(account,sub_account,item)
        if ledger is None:
            return None
        
        out_price = ledger.get_out_price_pa()
        
        return out_price
    
    def get_equal_idx(self,from_entry_id,from_line_no,from_idx):
        equal_idx = None
        for (idx,record) in enumerate(self.records):
            entry_id = record.get("entry_id",None)
            line_no = record.get("line_no",None)
            if (entry_id == from_entry_id) and (from_line_no == line_no) and (from_idx != idx):
                equal_idx = idx
                break
        return equal_idx
    
    def calc_diff_amount(self,entry_id,to_amount="dr_amount"):
        dr_amounts_with_entry_id = [record["dr_amount"] for record in self.records if record["entry_id"]==entry_id and ((type(record["dr_amount"]) is int) or(type(record["dr_amount"]) is float)) ]
        cr_amounts_with_entry_id = [record["cr_amount"] for record in self.records if record["entry_id"]==entry_id and ((type(record["cr_amount"]) is int) or(type(record["cr_amount"]) is float)) ]
        sum_dr_amounts = sum(dr_amounts_with_entry_id)
        sum_cr_amounts = sum(cr_amounts_with_entry_id)
        if to_amount == "dr_amount":
            return sum_cr_amounts - sum_dr_amounts
        elif to_amount == "cr_amount":
            return sum_dr_amounts - sum_cr_amounts
        raise ValueError("calc_diff_amount: you must specify 'dr_amount' or 'cr_amount' at param 'to_amount'.")
        return None
    
    def sort_records(self):
        # recordsを日付順（昇順）にソートする　日付が同じ場合は、仕訳番号順（昇順）とする
        self.records = sorted(self.records,key=lambda record : (record.get("datetime",""),record.get("entry_id",0)))
    
                              #<record>
    # 期首残高は、memo　key:KIND　value:OPENINGを指定して表現   &KIND::OPENING
    # 決算整理は、mono key:KIND　value:ADJUSTINGを指定して表現  &KIND::ADJUSTING
    # remarksは仕訳のremarks と各勘定のremarks を連結したもの
    # datetime :<datetime>
    # account
    # sub_account
    # item
    # partner
    # person_in_charge
    # memo:[]
    # remarks
    # quantity_unit
    # amount_unit          
    # dr_quantity
    # dr_amount
    # cr_quantity
    # cr_amount        
    def recalc_all(self):
        #再計算前に日付順・仕訳番号にソートする
        self.sort_records()
        
        q_ma = ItemQueueMA()
        q_fifo = ItemQueueFIFO()
        entry_id = -1
        for (idx,record) in enumerate(self.records):
            last_entry_id = entry_id
            entry_id = record.get("entry_id",None)
            
            if (last_entry_id != entry_id):
                op_equal_amount_passed = [] ## refreshed for each journal entry
                op_diff_amount_passed = []
                
            #accountは指定されている必要がある
            account = record.get("account",None) 
            if account is None:
                continue
            
            #sub_accountは指定されている必要がある
            #sub_accountを指定しない場合は{"sub_account":""}としておく
            sub_account = record.get("sub_account",None)
            if sub_account is None:
                continue
                
            #itemは指定されている必要がある
            #itemを指定しない場合は{"item":""}としておく                
            item = record.get("item",None)
            if item is None:
                continue
            
            side = self.accInfo.get_item_side(account,sub_account,item)
            
            #OP_BALANCE_QUANTITY
            dr_quantity = record.get("dr_quantity",None)
            if dr_quantity == "OP_BALANCE_QUANTITY":
                balance_quantity = self.get_balance_quantity(idx,side)
                self.records[idx]["dr_quantity"] = balance_quantity
                
            cr_quantity = record.get("cr_quantity",None)    
            if cr_quantity == "OP_BALANCE_QUANTITY":
                balance_quantity = self.get_balance_quantity(idx,side)
                self.records[idx]["cr_quantity"] = balance_quantity
            
            
            #OP_AUTO_AMOUNT
            method = self.accInfo.get_item_method(account,sub_account,item)
            
            dr_quantity = record.get("dr_quantity",None)
            dr_amount = record.get("dr_amount",None)
            if method=="LPC":
                if dr_amount=="OP_AUTO_AMOUNT":
                    out_price = self.get_out_price_lpc(account,sub_account,item)
                    self.records[idx]["dr_amount"] = dr_quantity * out_price
            elif method=="PA":
                if dr_amount=="OP_AUTO_AMOUNT":
                    out_price = self.get_out_price_pa(account,sub_account,item)
                    self.records[idx]["dr_amount"] = dr_quantity * out_price
            elif method=="MA":
                if dr_amount=="OP_AUTO_AMOUNT":
                    if side == "Dr":
                        out_quantity,out_amount = q_ma.get(account,sub_account,item,-dr_quantity)
                        self.records[idx]["dr_quantity"]=-out_quantity
                        self.records[idx]["dr_amount"]=-out_amount                        
                    elif side =="Cr":
                        out_quantity,out_amount = q_ma.get(account,sub_account,item,dr_quantity)
                        self.records[idx]["dr_quantity"]=out_quantity
                        self.records[idx]["dr_amount"]=out_amount
                elif (type(dr_amount) is int) or (type(dr_amount) is float):
                    if side == "Dr":
                        q_ma.put(account,sub_account,item,dr_quantity,dr_amount)
                    elif side =="Cr":
                        q_ma.put(account,sub_account,item,-dr_quantity,-dr_amount)
                else:
                    #dr_amount is None
                    pass
            elif method=="FIFO":
                if dr_amount=="OP_AUTO_AMOUNT":
                    if side == "Dr":
                        out_quantity,out_amount = q_fifo.get(account,sub_account,item,-dr_quantity)
                        self.records[idx]["dr_quantity"]=-out_quantity
                        self.records[idx]["dr_amount"]=-out_amount                        
                    elif side =="Cr":
                        out_quantity,out_amount = q_fifo.get(account,sub_account,item,dr_quantity)
                        self.records[idx]["dr_quantity"]=out_quantity
                        self.records[idx]["dr_amount"]=out_amount
                elif (type(dr_amount) is int) or (type(dr_amount) is float):
                    if side == "Dr":
                        q_fifo.put(account,sub_account,item,dr_quantity,dr_amount)
                    elif side =="Cr":
                        q_fifo.put(account,sub_account,item,-dr_quantity,-dr_amount)
                else:
                    #dr_amount is None
                    pass
            else:
                pass
                
            cr_quantity = record.get("cr_quantity",None)
            cr_amount = record.get("cr_amount",None)
            if method=="LPC":
                if cr_amount=="OP_AUTO_AMOUNT":
                    out_price = self.get_out_price_lpc(account,sub_account,item)
                    self.records[idx]["cr_amount"] = cr_quantity * out_price
            elif method=="PA":
                if cr_amount=="OP_AUTO_AMOUNT":
                    out_price = self.get_out_price_pa(account,sub_account,item)
                    self.records[idx]["cr_amount"] = cr_quantity * out_price
            elif method=="MA":
                if cr_amount=="OP_AUTO_AMOUNT":
                    if side == "Dr":
                        out_quantity,out_amount = q_ma.get(account,sub_account,item,cr_quantity)
                        self.records[idx]["cr_quantity"]=out_quantity
                        self.records[idx]["cr_amount"]=out_amount                        
                    elif side =="Cr":
                        out_quantity,out_amount = q_ma.get(account,sub_account,item,-cr_quantity)
                        self.records[idx]["cr_quantity"]=-out_quantity
                        self.records[idx]["cr_amount"]=-out_amount
                elif (type(cr_amount) is int) or (type(cr_amount) is float):
                    if side == "Dr":
                        q_ma.put(account,sub_account,item,-cr_quantity,-cr_amount)
                    elif side =="Cr":
                        q_ma.put(account,sub_account,item,cr_quantity,cr_amount)
                else:
                    #cr_amount is None
                    pass
                        
            elif method=="FIFO":
                if cr_amount=="OP_AUTO_AMOUNT":
                    if side == "Dr":
                        out_quantity,out_amount = q_fifo.get(account,sub_account,item,cr_quantity)
                        self.records[idx]["cr_quantity"]=out_quantity
                        self.records[idx]["cr_amount"]=out_amount                        
                    elif side =="Cr":
                        out_quantity,out_amount = q_fifo.get(account,sub_account,item,-cr_quantity)
                        self.records[idx]["cr_quantity"]=-out_quantity
                        self.records[idx]["cr_amount"]=-out_amount
                elif (type(cr_amount) is int) or (type(cr_amount) is float):
                    if side == "Dr":
                        q_fifo.put(account,sub_account,item,-cr_quantity,-cr_amount)
                    elif side =="Cr":
                        q_fifo.put(account,sub_account,item,cr_quantity,cr_amount)
                else:
                    #cr_amount is None
                    pass
            else:
                pass
            
            #OP_BALANCE_AMOUNT
            dr_amount = record.get("dr_amount",None)
            if dr_amount == "OP_BALANCE_AMOUNT":
                balance_amount = self.get_balance_amount(idx,side)
                #print("balance_amount",balance_amount)
                #print("idx",idx)
                #print("side",side)
                self.records[idx]["dr_amount"] = balance_amount
            
            cr_amount = record.get("cr_amount",None)
            if cr_amount == "OP_BALANCE_AMOUNT":
                balance_amount = self.get_balance_amount(idx,side)
                self.records[idx]["cr_amount"] = balance_amount
                
            #OP_EQUAL_AMOUNT
            dr_amount = record.get("dr_amount",None)
            cr_amount = record.get("cr_amount",None)
            line_no = record.get("line_no",None)
            if dr_amount=="OP_EQUAL_AMOUNT":
                equal_idx=self.get_equal_idx(entry_id,line_no,idx)
                if equal_idx is None:
                    raise ValueError('OP_EQUAL_AMOUNT: equal amount not foound.')
                if equal_idx < idx:
                    equal_amount=self.records[equal_idx]["cr_amount"]
                    self.records[idx]["dr_amount"]=equal_amount
                elif equal_idx > idx:
                    op_equal_amount_passed.append((equal_idx,"cr_amount",idx,"dr_amount")) # form equal_idx cr_amount to idx dr_amount
            if cr_amount=="OP_EQUAL_AMOUNT":
                equal_idx=self.get_equal_idx(entry_id,line_no,idx)
                if equal_idx is None:
                    raise ValueError('OP_EQUAL_AMOUNT: equal amount not found.')
                if equal_idx < idx:
                    equal_amount=self.records[equal_idx]["dr_amount"]
                    self.records[idx]["cr_amount"]=equal_amount
                elif equal_idx > idx:
                    op_equal_amount_passed.append((equal_idx,"dr_amount",idx,"cr_amount")) # form equal_idx dr_amount to idx cr_amount
            for (from_idx,from_amount,to_idx,to_amount) in op_equal_amount_passed:
                if idx == from_idx:
                    equal_amount=self.records[from_idx][from_amount]
                    self.records[to_idx][to_amount]=equal_amount                    
                
            #OP_DIFF_AMOUNT
            dr_amount = record.get("dr_amount",None)
            cr_amount = record.get("cr_amount",None)
            if dr_amount=="OP_DIFF_AMOUNT":
                op_diff_amount_passed.append((idx,"dr_amount"))
            if cr_amount=="OP_DIFF_AMOUNT":
                op_diff_amount_passed.append((idx,"cr_amount"))
            if len(op_diff_amount_passed)>=2:
                raise ValueError('OP_DIFF_AMOUNT: More than 2 OP_DIFF_AMOUNT are found in the journal enrtry. The operator can be specified only once in the journal enrtry.')
            if len(op_diff_amount_passed)==0:
                continue
            counts_dr_cr = record.get("counts_dr_cr",None)
            if counts_dr_cr is None:
                raise ValueError("OP_DIFF_AMOUNT: 'counts_dr_cr' must be specified.")
            if counts_dr_cr <= 0:
                continue
            order_id = record.get("order_id",None)
            if order_id is None:
                raise ValueError("OP_DIFF_AMOUNT: 'order_id' must be specified.")
            #OP_DIFF_AMOUNT is executed at the end of the journal entry.
            if order_id==counts_dr_cr - 1:
                to_idx,to_amount = op_diff_amount_passed[0]
                diff_amount = self.calc_diff_amount(entry_id,to_amount)
                self.records[to_idx][to_amount]=diff_amount

class  InterpretBaseTree(Interpreter):
    
    def param_pair(self, tree):
        #param_pair: param_mark param
        
        #param_mark
        param_mark = self.visit(tree.children[0])
        #param
        param = self.visit(tree.children[1])
        return (param_mark,param)
    
    def param_mark(self,tree):
        #param_mark: PARTNER_MARK | PERSON_IN_CHARGE_MARK | MEMO_MARK | REMARKS_MARK
        return tree.children[0].type
    
    def param(self,tree):
        #param: string | memo_number | memo_string | ref_memo
        return self.visit(tree.children[0])
    
    def string(self,tree):
        #string:STRING
        return tree.children[0].value
    
    def memo_number(self, tree):
        #memo_number: key ":" number memo_unit?
        memo_unit = None
        res_dic={}
        key = self.visit(tree.children[0])
        number = self.visit(tree.children[1])
        if len(tree.children)>=3:
            memo_unit = self.visit(tree.children[2])
        res_dic[key] = (number,memo_unit)
        return res_dic

    def memo_string(self, tree):
        #memo_string: key "::" STRING
        res_dic={}
        key = self.visit(tree.children[0])
        value_str = tree.children[1].value
        #print("memo_string key:",key,"value_str:",value_str)
        res_dic[key] = value_str
        return res_dic
    
    def key(self, tree):
        #key: STRING
        return tree.children[0].value
    
    def number(self, tree):
        #number: NUMBER
        #remove ',' and '_'
        #if number contains '.' then return float value, else return int value.
        value_str = tree.children[0].value
        value_str_rm = value_str.translate(str.maketrans({',': None, '_': None}))
        if "." in value_str_rm:
            ##float
            value = float(value_str_rm)
        else:
            ##int
            value = int(value_str_rm)
        return value
    
    def memo_unit(self, tree):
        #memo_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return tree.children[0].value

    def op_quantity(self, tree):
        #op_quantity: OP_EQUAL_QUANTITY | OP_BALANCE_QUANTITY | OP_DIFF_QUANTITY
        return tree.children[0].type
    
    def quantity_unit(self, tree):
        #quantity_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return tree.children[0].value

    def op_amount(self, tree):
        #op_amount: OP_AUTO_AMOUNT | OP_BALANCE_AMOUNT | OP_DIFF_AMOUNT | OP_EQUAL_AMOUNT
        return tree.children[0].type
    
    def amount_unit(self, tree):
        #amount_unit: STRING_AND_MARK_WITHOUT_DIGIT
        return tree.children[0].value

    def datetime(self, tree):
        #datetime: DATETIME
        return tree.children[0].value
    
    def account(self, tree):
        #account: STRING
        return tree.children[0].value
    
    def sub_account(self, tree):
        #sub_account: STRING | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                return ref_memo
            else:
                raise ValueError('sub_account must be string or ref_memo.')
        elif isinstance(c,Token):
            return c.value
        
        return None

    def item(self, tree):
        #item: STRING | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                return ref_memo
        elif isinstance(c,Token):
            return c.value
        
        raise ValueError('item must be string or ref_memo.')
        return None
    
    def price(self, tree):
        #price: number | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                return ref_memo
            elif c.data =="number":
                price = self.visit(c)
                return price

        raise ValueError('price must be number or ref_memo.')
        return None
    
    def quantity(self, tree):
        #quantity: number | op_quantity | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                return ref_memo
            elif c.data =="number":
                quantity = self.visit(c)
                return quantity
            elif c.data =="op_quantity":
                op_quantity = self.visit(c)
                return op_quantity
            
        raise ValueError('quantity must be number or operator or ref_memo.')        
        return None

    def amount(self, tree):
        #amount: number | op_amount | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                return ref_memo
            elif c.data =="number":
                number = self.visit(c)
                return number
            elif c.data =="op_amount":
                op_amount = self.visit(c)
                return op_amount
        
        raise ValueError('amount must be number or ref_memo or operator.')
        return None

    def ref_memo(self, tree):
        #ref_memo: "[" STRING "]"
        return {"ref_memo":tree.children[0].value}
 
    def entry_header(self,tree):
        #entry_header: _ENTRY_START_MARK  datetime param_pair*
        #entry_header = {"memo":{}}
                    
        entry_header = {}        
        for c in tree.children:
            if c.data=="datetime":
                date_or_datetime = self.visit(c)
                entry_header["datetime"]=date_or_datetime
            
            if c.data=="param_pair":
                param_mark,param = self.visit(c)
                if param_mark=='PARTNER_MARK':
                    entry_header["partner"]=param
                elif param_mark=='PERSON_IN_CHARGE_MARK':
                    entry_header["person_in_charge"]=param
                elif param_mark=='MEMO_MARK':
                    #entry_header["memo"].update(param)
                    if "memo" in entry_header:
                        entry_header["memo"].update(param)
                    else:
                        entry_header["memo"]=param
                elif param_mark=='REMARKS_MARK':
                    entry_header["remarks"]=param
                else:
                    pass
        return entry_header

    def debit(self, tree):
        #debit:  DEBIT_SIGN   #    "partner":"ABC", (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
                    
        debit = {}
        for c in tree.children:
            if c.data=="account":
                account = self.visit(c)
                debit["account"] = account
            elif c.data=="sub_account":
                sub_account = self.visit(c)
                debit["sub_account"] = sub_account         
            elif c.data=="item":
                item = self.visit(c)
                debit["item"] = item                 
            elif c.data=="price":
                price = self.visit(c)
                debit["price"] = price  
            elif c.data=="quantity":
                quantity = self.visit(c)
                debit["quantity"] = quantity  
            elif c.data=="quantity_unit":
                quantity_unit = self.visit(c)
                debit["quantity_unit"] = quantity_unit              
            elif c.data=="amount":
                amount = self.visit(c)
                debit["amount"] = amount                  
            elif c.data=="amount_unit":
                amount_unit = self.visit(c)
                debit["amount_unit"] = amount_unit              
            elif c.data=="param_pair":
                param_mark,param = self.visit(c)
                if param_mark=='PARTNER_MARK':
                    debit["partner"]=param
                elif param_mark=='PERSON_IN_CHARGE_MARK':
                    debit["person_in_charge"]=param
                elif param_mark=='MEMO_MARK':
                    #debit["memo"].update(param)
                    if "memo" in debit:
                        debit["memo"].update(param)
                    else:
                        debit["memo"]= param
                elif param_mark=='REMARKS_MARK':
                    debit["remarks"]=param
                else:
                    pass                
            else:
                pass
        return debit

    def credit(self, tree):
        #credit: CREDIT_SIGN  account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*                    

        credit = {}
        for c in tree.children:
            if c.data=="account":
                account = self.visit(c)
                credit["account"] = account
            elif c.data=="sub_account":
                sub_account = self.visit(c)
                credit["sub_account"] = sub_account         
            elif c.data=="item":
                item = self.visit(c)
                credit["item"] = item                 
            elif c.data=="price":
                price = self.visit(c)
                credit["price"] = price  
            elif c.data=="quantity":
                quantity = self.visit(c)
                credit["quantity"] = quantity  
            elif c.data=="quantity_unit":
                quantity_unit = self.visit(c)
                credit["quantity_unit"] = quantity_unit              
            elif c.data=="amount":
                amount = self.visit(c)
                credit["amount"] = amount                  
            elif c.data=="amount_unit":
                amount_unit = self.visit(c)
                credit["amount_unit"] = amount_unit              
            elif c.data=="param_pair":
                param_mark,param = self.visit(c)
                if param_mark=='PARTNER_MARK':
                    credit["partner"]=param
                elif param_mark=='PERSON_IN_CHARGE_MARK':
                    credit["person_in_charge"]=param
                elif param_mark=='MEMO_MARK':
                    #credit["memo"].update(param)
                    if "memo" in credit:
                        credit["memo"].update(param)
                    else:
                        credit["memo"]=param
                elif param_mark=='REMARKS_MARK':
                    credit["remarks"]=param
                else:
                    pass                
            else:
                pass
        return credit
    
    def entry_footer(self, tree):
        #entry_footer: _ENTRY_END_MARK
        entry_footer = {}
        return entry_footer
    
    def text(self,tree):
        # text: TEXT
        return tree.children[0].value
    
class  InterpretJournalTree(InterpretBaseTree):
    def __init__(self):
        self.entry_id =0
        pass

    def get_ledgers(self,tree_journal):
        
        lgs = Ledgers()
        
        #get journal ref_memo filled
        journal = self.visit(tree_journal)
        for journal_entry in journal["journal_entries"]:
            lgs.register(journal_entry)
        lgs.recalc_all()
        return lgs

    def get_str_datetime_from_tree_journal_entry(self,tree_journal_entry):
        for c in tree_journal_entry.children:
            if c.data =="entry_header":
                for cc in c.children:
                    if cc.data=="datetime":
                        return cc.children[0].value
        return ''

    def journal(self, tree):
        # journal: (text* journal_entry)* text*
        #{journal_entries:[{},{},...],"texts":["Hello","Hi",...]}
        self.memo_global={}
        journal = {"journal_entries":[],"texts":[]}
        #journal: (text* journal_entry)* text*
        tree_journal_entries = [c for c in tree.children if c.data=="journal_entry"]
        tree_texts = [c for c in tree.children if c.data=="text"]
        
        #journal_entries
        sorted_children = sorted(tree_journal_entries,key = self.get_str_datetime_from_tree_journal_entry)
        for c in sorted_children:
            # get journal_entry with ref_memo filled.
            journal_entry = self.visit(c)
            if ("debit" not in journal_entry) and ("credit" not in journal_entry):
                    #update memo_global with journal_entry
                    # that only contains entry_header.
                    # If that entry_header contains ref_memo,
                    # that refer to the memo until the header, not the memo on the header. 
                    #print("journal")
                    #print("self.memo_global",self.memo_global)
                    #print("self.memo_journal_entry",self.memo_journal_entry)
                    self.memo_global.update(self.memo_journal_entry)
                    #print("self.memo_global(updated)",self.memo_global)
            journal_entry["entry_header"]["entry_id"] = self.entry_id
            journal["journal_entries"].append(journal_entry)
            self.entry_id +=1
        
        #texts
        for c in tree_texts:
            text = self.visit(c)
            journal["texts"].append(text)
            
        return journal

    def journal_entry(self, tree):
        #journal_entry: entry_header (debit | credit)* entry_footer
        
        #{"entry_header":{
        #    "datetime":"2023-01-01",
        #    "partner":"ABC",
        #    "person_in_charge":"Mr_D",
        #    "memo":{"key":"value1","key2",(12,"個"),...},
        #    "remarks":"This is remark"},
        # "debit":[{
        #    "account":"商品",
        #    "sub_account":"ズボン",
        #    "item":"itemA",
        #    "price":123,
        #    "quantity":3,
        #    "quantity_unit":"itemA",
        #    "amount":"itemA",
        #    "amount_unit":"itemA",
        #    "partner":"DEF",
        #    "person_in_charge":"Mr_D",
        #    "memo":{"key":"value1","key2",(12,"個"),...},
        #    "remarks":"This is remark"},{},{},....],        
        # "credit":[{},{},...], #same as debit
        # "entry_footer":{}}
        self.memo_journal_entry ={}
        journal_entry = {}
        order_id = 0
        debit_line_no = 0
        credit_line_no = 0
        for c in tree.children:
            if c.data=="entry_header":
                entry_header = self.visit(c)
                journal_entry["entry_header"]=entry_header
            elif c.data=="debit":
                debit = self.visit(c)
                debit["order_id"]=order_id
                debit["line_no"]=debit_line_no
                order_id += 1
                debit_line_no +=1
                if "debit" not in journal_entry:
                    journal_entry["debit"]=[debit]
                else:
                    journal_entry["debit"].append(debit)
            elif c.data=="credit":
                credit = self.visit(c)
                credit["order_id"]=order_id
                credit["line_no"]=credit_line_no
                order_id += 1
                credit_line_no += 1
                if "credit" not in journal_entry:
                    journal_entry["credit"]=[credit]
                else:
                    journal_entry["credit"].append(credit)                
            elif c.data=="entry_footer":
                entry_footer = self.visit(c)
                journal_entry["entry_footer"]=entry_footer
                
            #journal_entry["entry_header"]["counts_dr_cr"]=order_id #number of Dr and Cr
        return journal_entry
    
    def entry_header(self,tree):
        #entry_header: _ENTRY_START_MARK  datetime param_pair*
        #entry_header = {"memo":{}}
        
        for c in tree.children:
            if c.data=="param_pair":
                param_mark,param = self.visit(c)
                if param_mark=='MEMO_MARK':
                    self.memo_journal_entry.update(param)
                    
        entry_header = super().entry_header(tree)    
        
        return entry_header
    
    def debit(self, tree):
        #debit:  DEBIT_SIGN   #    "partner":"ABC", (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        self.memo_local = {}
        #debit = {"memo":{}}
        ## caliculate memo first to caiculate ref_memo next.
        for c in tree.children:
            if c.data=="param_pair":
                param_mark,param = self.visit(c)
                if param_mark=='MEMO_MARK':
                    self.memo_local.update(param)
        
        debit = super().debit(tree)

        return debit
    
    def credit(self, tree):
        #credit: CREDIT_SIGN  account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        self.memo_local = {}
        #credit = {"memo":{}}
        
        ## calicute memo first to caiculate ref_memo next.
        for c in tree.children:
            if c.data=="param_pair":
                param_mark,param = self.visit(c)
                if param_mark=='MEMO_MARK':
                    self.memo_local.update(param)
        
        credit = super().credit(tree)
        
        return credit
    
    def sub_account(self, tree):
        #sub_account: STRING | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                if type(ref_memo) is str:
                    return ref_memo
                else:
                    raise ValueError('sub_account must be string.')
        elif isinstance(c,Token):
            return c.value
        
        return None

    def item(self, tree):
        #item: STRING | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                if type(ref_memo) is str:
                    return ref_memo
                else:
                    raise ValueError('item must be string.')
        elif isinstance(c,Token):
            return c.value
        
        return None

    def price(self, tree):
        #price: number | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                if type(ref_memo) is tuple and len(ref_memo)>=2:
                    if (type(ref_memo[0]) is float) or (type(ref_memo[0]) is int):
                        # price_unit is ignored
                        # todo convert price from price_unit
                        return ref_memo[0]
                raise ValueError('price must be number.')
            elif c.data =="number":
                price = self.visit(c)
                return price
        else:
            raise ValueError('price must be number.')
        
    def quantity(self, tree):
        #quantity: number | op_quantity | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                if type(ref_memo) is tuple and len(ref_memo)>=2:
                    if (type(ref_memo[0]) is float) or (type(ref_memo[0]) is int):
                        # unit is ignored
                        # todo convert quantity from quantity_unit
                        return ref_memo[0]
                raise ValueError('quantity must be number or operator.')
            elif c.data =="number":
                quantity = self.visit(c)
                return quantity
            elif c.data =="op_quantity":
                op_quantity = self.visit(c)
                return op_quantity
        else:
            raise ValueError('quantity must be number or operator.')        
    
    
    def amount(self, tree):
        #amount: number | op_amount | ref_memo
        c = tree.children[0]
        if isinstance(c,Tree): 
            if c.data =="ref_memo":
                ref_memo = self.visit(c)
                if type(ref_memo) is tuple and len(ref_memo)>=2:
                    if (type(ref_memo[0]) is float) or (type(ref_memo[0]) is int):
                        # unit is ignored
                        # todo convert quantity from quantity_unit
                        return ref_memo[0]
                raise ValueError('amount must be number or ref_number or operator.')
            elif c.data =="number":
                amount = self.visit(c)
                return amount
            elif c.data =="op_amount":
                op_amount = self.visit(c)
                return op_amount
        else:
            raise ValueError('amount must be number or ref_number or operator.')
        
    def ref_memo(self, tree):
        #ref_memo: "[" STRING "]"
        #実際の値に変換して返す
        c = tree.children[0]
        key = c.value
        value = self.getMemoValue(key)
        #print("getMemoValue key:",key,"value:",value)
        return value
    
    def getMemoValue(self,key):
        #print("getMemoValue")
        #print("self.memo_local",self.memo_local)
        #print("self.memo_journal_entry",self.memo_journal_entry)
        #print("self.memo_global:",self.memo_global)
        #print("key",key)
        if key in self.memo_local:
            return self.memo_local[key]
        elif key in self.memo_journal_entry:
            return self.memo_journal_entry[key]
        elif key in self.memo_global:
            return self.memo_global[key]
        else:
            return None


class QTYJournalDicToTree:
    def __init__(self):
        self.default_json_filename="QTYjournalDic.json"
        
    def save_json(self,journal_dic,filename=None):
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), ACCOUNT_INFO_FILENAME)
            filename = os.path.join(Path().resolve(), self.default_json_filename)

        with open(filename, 'w', newline=None,encoding='utf-8') as f:
            json.dump(journal_dic,f,ensure_ascii=False,indent=2)
            
    def load_json(self,filename=None):
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), ACCOUNT_INFO_FILENAME)
            filename = os.path.join(Path().resolve(), self.default_json_filename)
        with open(filename, 'r', newline=None,encoding='utf-8') as f:
            journal_dic = json.load(f)
            
        return journal_dic

    def load_json_to_tree(self,filename=None):
        
        journal_dic = self.load_json(filename)
        journal_tree = self.translate(journal_dic)
        
        return journal_tree
    
    def translate(self,journal_dic):
        ##journal
        #Tree(Token('RULE', 'journal'), [Token('DATETIME', '2021-12-03')])
        
        journal_list =journal_dic.get("journal",None)
        if journal_list is not None:
            data = Token("RULE","journal")
            children = self.make_children_from_journai_list(journal_list)
            return Tree(data,children)

    def make_children_from_journai_list(self,journal_list):
        children =[]
        for entry in journal_list:
            if "journal_entry" in entry:
                journal_entry_dic = entry["journal_entry"]
                journal_entry_data = Token("RULE","journal_entry")
                journal_entry_children = self.make_children_from_journal_entry_dic(journal_entry_dic)
                children.append(Tree(journal_entry_data,journal_entry_children))
        return children
            
    def make_children_from_journal_entry_dic(self,journal_entry_dic):
        children =[]
        ##entry_header
        entry_header_dic = journal_entry_dic.get("entry_header",None)
        if entry_header_dic is not None:
            entry_header_data = Token("RULE","entry_header")
            entry_header_children = self.make_children_from_journal_entry_header_dic(entry_header_dic)
            children.append(Tree(entry_header_data,entry_header_children))

        #body
        body_list = journal_entry_dic.get("body",None)
        if body_list is not None:
            for debit_or_credit in body_list:
                debit_dic = debit_or_credit.get("debit",None)
                if debit_dic is not None:
                    debit_data = Token("RULE","debit")
                    debit_children = self.make_children_from_debit_or_credit_dic(debit_dic)
                    children.append(Tree(debit_data,debit_children))
                credit_dic = debit_or_credit.get("credit",None)
                if credit_dic is not None:
                    credit_data = Token("RULE","credit")
                    credit_children = self.make_children_from_debit_or_credit_dic(credit_dic)
                    children.append(Tree(credit_data,credit_children))            
        ## entry_footer
        entry_footer_dic = journal_entry_dic.get("entry_footer",None)
        if entry_footer_dic is not None:
            entry_footer_data = Token("RULE","entry_footer")
            entry_footer_children = self.make_children_from_journal_entry_footer_dic(entry_footer_dic)
            children.append(Tree(entry_footer_data,entry_footer_children))
        
        return children
    
    def make_children_from_journal_entry_header_dic(self,entry_header_dic):
        children =[]
        #datetime
        #datetime: DATETIME
        datetime = entry_header_dic.get("datetime",None)
        if datetime is not None:
            children.append(Tree(Token('RULE', 'datetime'), [Token('DATETIME', datetime)]))
        #param_pair
        #param_pair: param_mark param
        #param_mark: PARTNER_MARK | PERSON_IN_CHARGE_MARK | MEMO_MARK | REMARKS_MARK
        #param: string | memo_number | memo_string | ref_memo
        #partner
        partner = entry_header_dic.get("partner",None)
        # string | ref_memo
        if partner is not None:
            partner_data = Token("RULE","param_pair")
            if type(partner) is str:
                partner_children = [Tree(Token('RULE', 'param_mark'),[Token('PERTNER_MARK', '$')]),
                                    Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'string'), [Token('STRING', partner)])])]
                children.append(Tree(partner_data,partner_children))
            if type(partner) is dict:
                if "ref_memo" in partner:
                    partner_children =[Tree(Token('RULE', 'param_mark'), [Token('PARTNER_MARK', '$')]),
                                       Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'ref_memo'), [Token('STRING',partner.get("ref_memo",None))])])]
                    children.append(Tree(partner_data,partner_children))
        #person_in_charge
        person_in_charge = entry_header_dic.get("person_in_charge",None)
        # string | ref_memo
        if person_in_charge is not None:
            person_in_charge_data = Token("RULE","param_pair")
            if type(person_in_charge) is str:
                person_in_charge_children = [Tree(Token('RULE', 'param_mark'),[Token('PERSON_IN_CHARGE_MARK', '>')]),
                                    Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'string'), [Token('STRING', person_in_charge)])])]
                children.append(Tree(person_in_charge_data,person_in_charge_children))
            if type(person_in_charge) is dict:
                if "ref_memo" in person_in_charge:
                    person_in_charger_children =[Tree(Token('RULE', 'param_mark'), [Token('PERSON_IN_CHARGE_MARK', '>')]),
                                       Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'ref_memo'), [Token('STRING',person_in_charge.get("ref_memo",None))])])]
                    children.append(Tree(person_in_charge_data,person_in_charge_children))
                    
        #memo
        memo = entry_header_dic.get("memo",None)
        if memo is not None:
            for k,v in memo.items():
                memo_data = Token("RULE","param_pair")
                if type(v) is tuple:
                    memo_children = [Tree(Token('RULE', 'param_mark'), [Token('MEMO_MARK', '&')]),
                                     Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'memo_number'), [Tree(Token('RULE', 'key'), [Token('STRING',k)]), Tree(Token('RULE', 'number'), [Token('NUMBER', str(v[0]))]), Tree(Token('RULE', 'memo_unit'), [Token('STRING_AND_MARK_WITHOUT_DIGIT', v[1])])])])]
                elif type(v) is str:
                    memo_children = [Tree(Token('RULE', 'param_mark'), [Token('MEMO_MARK', '&')]),
                                     Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'memo_string'), [Tree(Token('RULE', 'key'), [Token('STRING', k)]), Token('STRING', v)])])]
                children.append(Tree(memo_data,memo_children))
        
        #remarks
        # string
        remarks = entry_header_dic.get("remarks",None)
        if remarks is not None:
            remarks_data = Token("RULE","param_pair")
            memo_children = [Tree(Token('RULE', 'param_mark'), [Token('REMARKS_MARK', '##')]),
                             Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'string'), [Token('STRING', remarks)])])]
            children.append(Tree(remarks_data,memo_children))
            
        return children
    
    def get_op_amount_mark(self,signature):
        return JournalDicToText().get_op_amount_mark(signature)

    def make_children_from_debit_or_credit_dic(self,debit_or_credit_dic):
        children =[]
        #account
        #account: STRING
        account = debit_or_credit_dic.get("account",None)
        if account is not None:
            account_data = Token("RULE","account")
            account_children = [Token('STRING', account )]
            children.append(Tree(account_data,account_children))
            
        #sub_account
        #sub_account: STRING | ref_memo
        sub_account = debit_or_credit_dic.get("sub_account",None)
        if sub_account is not None:
            if type(sub_account) is str:
                sub_account_data =  Token("RULE","sub_account")
                sub_account_children = [Token('STRING', sub_account )]
                children.append(Tree(account_data,account_children))
            elif type(sub_account) is dict:
                if "ref_memo" in sub_account:
                    sub_account_children = [Tree(Token('RULE', 'ref_memo'), [Token('STRING', sub_account["ref_memo"])])]
                    children.append(Tree(account_data,account_children))
        #item
        #item: STRING | ref_memo
        item = debit_or_credit_dic.get("item",None)
        if item is not None:
            if type(item) is str:
                item_data =  Token("RULE","item")
                item_children = [Token('STRING', item )]
                children.append(Tree(item_data,item_children))
            elif type(item) is dict:
                if "ref_memo" in item:
                    item_data =  Token("RULE","item")
                    item_children = [Tree(Token('RULE', 'ref_memo'), [Token('STRING', item["ref_memo"])])]
                    children.append(Tree(item_data,item_children))

        #price
        #price: number | ref_memo
        price = debit_or_credit_dic.get("price",None)
        if price is not None:        
            if (type(price) is int) or (type(price) is float):
                price_data =  Token("RULE","price")
                price_children =  [Tree(Token('RULE', 'number'), [Token('NUMBER', str(price))])]
                children.append(Tree(price_data,price_children))
            elif type(price) is dict:
                if "ref_memo" in price:
                    price_data =  Token("RULE","price")
                    price_children =  [Tree(Token('RULE', 'ref_memo'), [Token('STRING', price["ref_memo"])])]
                    children.append(Tree(price_data,price_children))                
                
        #quantity
        #quantity: number | op_quantity | ref_memo
        quantity = debit_or_credit_dic.get("quantity",None)
        if quantity is not None:        
            if (type(quantity) is int) or (type(quantity) is float):
                quantity_data =  Token("RULE","quantity")
                quantity_children =  [Tree(Token('RULE', 'number'), [Token('NUMBER', str(quantity))])]
                children.append(Tree(quantity_data,quantity_children))
            elif type(quantity) is str:
                mark = self.get_op_quantity_mark(quantity)
                if mark is not None:
                    quantity_data =  Token("RULE","quantity")
                    quantity_children =  [Tree(Token('RULE', 'op_quantity'), [Token(quantity, mark)])]
                    children.append(Tree(quantity_data,quantity_children))
            elif type(quantity) is dict:
                if "ref_memo" in quantity:
                    quantity_data =  Token("RULE","quantity")
                    quantity_children =  [Tree(Token('RULE', 'ref_memo'), [Token('STRING', quantity["ref_memo"])])]
                    children.append(Tree(quantity_data,quantity_children))  
            
        #quantity_unit
        #quantity_unit: STRING_AND_MARK_WITHOUT_DIGIT
        quantity_unit = debit_or_credit_dic.get("quantity_unit",None)
        if quantity_unit is not None: 
            quantity_unit_data=Token('RULE', 'quantity_unit')
            quantity_unit_children = [Token('STRING_AND_MARK_WITHOUT_DIGIT', quantity_unit)]
            children.append(Tree(quantity_unit_data,quantity_unit_children)) 
                
        #amount
        #amount: number | op_amount | ref_memo
        #op_amount: OP_AUTO_AMOUNT | OP_BALANCE_AMOUNT | OP_DIFF_AMOUNT | OP_EQUAL_AMOUNT
        amount = debit_or_credit_dic.get("amount",None)
        if amount is not None:        
            if (type(amount) is int) or (type(amount) is float):
                amount_data =  Token("RULE","amount")
                amount_children =  [Tree(Token('RULE', 'number'), [Token('NUMBER', str(amount))])]
                children.append(Tree(amount_data,amount_children))
            elif type(amount) is str:
                mark = self.get_op_amount_mark(amount)
                if mark is not None:
                    amount_data =  Token("RULE","amount")
                    amount_children =  [Tree(Token('RULE', 'op_amount'), [Token(amount, mark)])]
                    children.append(Tree(amount_data,amount_children))
            elif type(amount) is dict:
                if "ref_memo" in amount:
                    amount_data =  Token("RULE","amount")
                    amount_children =  [Tree(Token('RULE', 'ref_memo'), [Token('STRING', amount["ref_memo"])])]
                    children.append(Tree(amount_data,amount_children))  
    
        #amount_unit
        #amount_unit: STRING_AND_MARK_WITHOUT_DIGIT
        amount_unit = debit_or_credit_dic.get("amount_unit",None)
        if amount_unit is not None: 
            amount_unit_data=Token('RULE', 'amount_unit')
            amount_unit_children = [Token('STRING_AND_MARK_WITHOUT_DIGIT', amount_unit)]
            children.append(Tree(amount_unit_data,amount_unit_children)) 

        #param_pair
        #param_pair: param_mark param
        #param_mark: PARTNER_MARK | PERSON_IN_CHARGE_MARK | MEMO_MARK | REMARKS_MARK
        #param: string | memo_number | memo_string | ref_memo
        #partner
        partner = debit_or_credit_dic.get("partner",None)
        # string | ref_memo
        if partner is not None:
            partner_data = Token("RULE","param_pair")
            if type(partner) is str:
                partner_children = [Tree(Token('RULE', 'param_mark'),[Token('PERTNER_MARK', '$')]),
                                    Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'string'), [Token('STRING', partner)])])]
                children.append(Tree(partner_data,partner_children))
            if type(partner) is dict:
                if "ref_memo" in partner:
                    partner_children =[Tree(Token('RULE', 'param_mark'), [Token('PARTNER_MARK', '$')]),
                                       Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'ref_memo'), [Token('STRING',partner.get("ref_memo",None))])])]
                    children.append(Tree(partner_data,partner_children))
        #person_in_charge
        person_in_charge = debit_or_credit_dic.get("person_in_charge",None)
        # string | ref_memo
        if person_in_charge is not None:
            person_in_charge_data = Token("RULE","param_pair")
            if type(person_in_charge) is str:
                person_in_charge_children = [Tree(Token('RULE', 'param_mark'),[Token('PERSON_IN_CHARGE_MARK', '>')]),
                                    Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'string'), [Token('STRING', person_in_charge)])])]
                children.append(Tree(person_in_charge_data,person_in_charge_children))
            if type(person_in_charge) is dict:
                if "ref_memo" in person_in_charge:
                    person_in_charger_children =[Tree(Token('RULE', 'param_mark'), [Token('PERSON_IN_CHARGE_MARK', '>')]),
                                       Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'ref_memo'), [Token('STRING',person_in_charge.get("ref_memo",None))])])]
                    children.append(Tree(person_in_charge_data,person_in_charge_children))
                    
        #memo
        memo = debit_or_credit_dic.get("memo",None)
        if memo is not None:
            for k,v in memo.items():
                memo_data = Token("RULE","param_pair")
                if type(v) is tuple:
                    memo_children = [Tree(Token('RULE', 'param_mark'), [Token('MEMO_MARK', '&')]),
                                     Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'memo_number'), [Tree(Token('RULE', 'key'), [Token('STRING',k)]), Tree(Token('RULE', 'number'), [Token('NUMBER', str(v[0]))]), Tree(Token('RULE', 'memo_unit'), [Token('STRING_AND_MARK_WITHOUT_DIGIT', v[1])])])])]
                elif type(v) is str:
                    memo_children = [Tree(Token('RULE', 'param_mark'), [Token('MEMO_MARK', '&')]),
                                     Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'memo_string'), [Tree(Token('RULE', 'key'), [Token('STRING', k)]), Token('STRING', v)])])]
                children.append(Tree(memo_data,memo_children))
        
        #remarks
        # string
        remarks = debit_or_credit_dic.get("remarks",None)
        if remarks is not None:
            remarks_data = Token("RULE","param_pair")
            memo_children = [Tree(Token('RULE', 'param_mark'), [Token('REMARKS_MARK', '##')]),
                             Tree(Token('RULE', 'param'), [Tree(Token('RULE', 'string'), [Token('STRING', remarks)])])]
            children.append(Tree(remarks_data,memo_children))
            
        return children

    def make_children_from_journal_entry_footer_dic(self,entry_footer_dic):
        # nothing
        children = []
        return children

class JournalDicToText:
    def __init__(self):
        self.default_journal_filename="journal.txt"

    def save_journal_text(self,csv_tree,filename=None):
        journal_text = self.get_journal_text(csv_tree)
        if filename is None:
            # filename = os.path.join(os.path.dirname(__file__), ACCOUNT_INFO_FILENAME)
            filename = os.path.join(Path().resolve(), self.default_journal_filename)

        with open(filename, 'w', newline=None,encoding='utf-8') as f:
            f.write(journal_text)
    
    def get_op_quantity_mark(self,signature):
        op_quantity_dic = {"OP_BALANCE_QUANTITY":"*B","OP_DIFF_QUANTITY":"*D","OP_EQUAL_QUANTITY":"*E"}
        return op_quantity_dic.get(signature,None)

    def get_op_amount_mark(self,signature):
        op_amount_dic = {"OP_AUTO_AMOUNT":"?A","OP_BALANCE_AMOUNT":"?B","OP_DIFF_AMOUNT":"?D","OP_EQUAL_AMOUNT":"?E"}
        return op_amount_dic.get(signature,None)
    
    def get_ref_memo_str(self,ref_memo):
        if type(ref_memo) is not dict:
            return None
        ref_memo_str = ref_memo.get("ref_memo",None)
        if ref_memo_str is None:
            return None
        return "["+ref_memo_str+"]" 

    def get_header_text(self,entry_header):
        entry_text =""
        entry_text += "<<\n"

        datetime_str = entry_header.get("datetime",None)
        if datetime_str is not None:
            entry_text += datetime_str

        item_str = entry_header.get("item",None)
        if item_str is not None:
            entry_text += (" #"+item_str)

        partner_str = entry_header.get("partner",None)
        if partner_str is not None:
            entry_text += (" $"+partner_str)

        person_in_charge_str = entry_header.get("person_in_charge",None)
        if (person_in_charge_str is not None) and (person_in_charge_str!=""):
            #print("entry_header",entry_header)
            #print("person_in_charge_str",person_in_charge_str)
            entry_text += (" >"+person_in_charge_str)

        memo_dict = entry_header.get("memo",None)
        if memo_dict is not None:
            #print("memo_dict",memo_dict)
            for k,v in memo_dict.items():
                if type(v) is tuple and len(v)>=2:
                    str_memo_value = self.memo_value_to_str(v)
                    if str_memo_value is not None:
                        entry_text += (" &"+k+":"+str_memo_value)
                elif type(v) is str:
                    entry_text += (" &"+k+"::"+v)

        remarks_str = entry_header.get("remarks",None)
        if (remarks_str is not None) and (remarks_str !=""):
            entry_text += (" ##"+remarks_str)
        
        return entry_text
    
    def memo_value_to_str(self,memo_value):
        if type(memo_value) is not tuple:
            return None
        if len(memo_value)<=1:
            return None
        memo_value_str = str(memo_value[0])
        memo_value_unit = memo_value[1]
        if memo_value_unit is not None:
            memo_value_str += memo_value_unit
        return memo_value_str
    
    def get_debit_or_credit_text_from_entry(self,entry):
        
        entry_text = ""
        
        if "debit" in entry:
            debit_or_credit = entry["debit"]
            entry_text += " Dr"
        elif "credit"  in entry:
            debit_or_credit = entry["credit"]
            entry_text += " Cr"
        else:
            return None

        #account
        #account: STRING
        account =debit_or_credit.get("account",None)
        # account is required
        if account is None:
            return None
        entry_text += (" "+account)

        #sub_account
        #sub_account: STRING | ref_memo
        sub_account =debit_or_credit.get("sub_account",None)
        if sub_account is not None:
            if type(sub_account) is dict:
                ref_memo = self.get_ref_memo_str(sub_account)
                if ref_memo is not None:
                    entry_text += ("/"+ref_memo)
            elif type(sub_account) is str:
                entry_text += ("/"+sub_account)

        #item
        #item: STRING | ref_memo
        item =debit_or_credit.get("item",None)
        if item is not None:
            if type(item) is dict:
                ref_memo = self.get_ref_memo_str(item)
                if ref_memo is not None:
                    entry_text += ("#"+ref_memo)
            elif type(item) is str:
                entry_text += ("#"+item)

        #price
        #price: number | ref_memo
        price =debit_or_credit.get("price",None)
        if price is not None:
            if type(price) is dict:
                ref_memo = self.get_ref_memo_str(price)
                if ref_memo is not None:
                    entry_text += (" @"+ref_memo)
            elif (type(price) is int) or (type(price) is float):
                entry_text += (" @"+str(price))                        

        #quantity
        #quantity: number | op_quantity | ref_memo
        quantity =debit_or_credit.get("quantity",None)
        if quantity is not None:
            if type(quantity) is dict:
                ref_memo = self.get_ref_memo_str(quantity)
                if ref_memo is not None:
                    entry_text += (" *"+ref_memo)
            elif type(quantity) is str:
                #op_quantity
                entry_text += (" "+self.get_op_quantity_mark(quantity)) #*B *D *E
            elif (type(quantity) is int) or (type(quantity) is float):
                #number
                entry_text +=(" *"+str(quantity))

        #quantity_unit
        #quantity_unit: STRING_AND_MARK_WITHOUT_DIGIT
        quantity_unit =debit_or_credit.get("quantity_unit",None)
        if quantity_unit is not None:
            entry_text +=quantity_unit

        # amount
        # amount: number | op_amount | ref_memo
        amount =debit_or_credit.get("amount",None)
        if amount is not None:
            if type(amount) is dict:
                ref_memo = self.get_ref_memo_str(amount)
                if ref_memo is not None:
                    entry_text += (" *"+ref_memo)
            elif type(amount) is str:
                #op_amount
                #print("amount",amount)
                entry_text += (" "+self.get_op_amount_mark(amount)) #*A *B *E
            elif (type(amount) is int) or (type(amount) is float):
                #number
                entry_text +=(" "+str(amount))                            

        #amount_unit
        #amount_unit: STRING_AND_MARK_WITHOUT_DIGIT
        amount_unit =debit_or_credit.get("amount_unit",None)
        if amount_unit is not None:
            entry_text +=amount_unit

        #partner            
        partner_str = debit_or_credit.get("partner",None)
        if partner_str is not None:
            entry_text += (" $"+partner_str)

        #person_in_charge
        person_in_charge_str = debit_or_credit.get("person_in_charge",None)
        if person_in_charge_str is not None and person_in_charge_str !="":
            entry_text += (" >"+person_in_charge_str)

        #memo
        memo_dict = debit_or_credit.get("memo",None)
        if memo_dict is not None:
            for k,v in memo_dict.items():
                if type(v) is tuple and len(v)>=2:
                    str_memo_value = self.memo_value_to_str(v)
                    if str_memo_value is not None:
                        entry_text += (" &"+k+":"+str_memo_value)
                elif type(v) is str:
                    entry_text += (" &"+k+"::"+v)

        #remarks
        remarks_str = debit_or_credit.get("remarks",None)
        if remarks_str is not None and remarks_str!="":
            entry_text += (" ##"+remarks_str)
        
        return entry_text
    
    def get_text_from_journal_dic(self,journal_dic):
        journal_text =""
        journal = journal_dic.get("journal",[])
        for entry in journal:
            entry_text =""
            if type(entry) is not dict:
                continue
            if "journal_entry" not in entry:
                continue
            journal_entry = entry.get("journal_entry",None)
            if journal_entry is None:
                continue
                
            #header
            entry_header = journal_entry.get("entry_header",None)
            if entry_header is None:
                continue
            entry_text  = self.get_header_text(entry_header)   
            entry_text += "\n"
            
            #body
            #headerのみで、bodyがない場合もある
            body = journal_entry.get("body",[])
            for entry in body:
                debit_or_credit_text = self.get_debit_or_credit_text_from_entry(entry)
                if debit_or_credit_text is not None:
                    entry_text += debit_or_credit_text
                    entry_text += "\n"
                    
            #footer
            #entry_footer = journal_entry.get("entry_footer",None)
            #フッターの有無にかかわらす、_ENTRY_END_MARKを入れる
            entry_text += ">>\n"
            
            journal_text += entry_text
        
        return journal_text


def main():

    test_journal= r"""
以下に仕訳の例を示します。
仕訳の例１

<<
2022-12-12 &担当者::A君 &特売品::さといも &rate:100円 &販売上限:10個 &所持金額:2000円
>>
<<2022-12-14 ##test 
Dr　通信費/[担当者]　#[特売品] @600 ?B円 
Cr　現金 5000 ##test
Cr　預金 1000>>

"""
    journal_tree = QTYJournalToTree().translate(test_journal)
    print(journal_tree)

if __name__ == "__main__":
    main()

