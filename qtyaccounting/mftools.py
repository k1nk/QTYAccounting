# Copyright (c) 2022 Kenichi Nakatani
# This file is part of QTYAccounting.
# QTYAccounting is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
# QTYAccounting is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
# You should have received a copy of the GNU General Public License along with QTYAccounting. If not, see <https://www.gnu.org/licenses/>.
import os
from .qtytools import InterpretBaseTree,JournalDicToText,QTYJournalToTree,InterpretJournalTree,QTYJournalDicToTree
from pathlib import Path
from lark import Lark

class MfCSVToCSVTree:
    """
    マネーフォワードののCSVファイルからCSVの構文木を作成する
    摘要欄に数量簿記の数量等の情報を記入して解析するため
    """
    tekiyou_def_str = r"""
        tekiyou: tekiyou_entry?
        tekiyou_entry: entry_header (debit | credit)+ entry_footer
        entry_header: _ENTRY_START_MARK (prefixed_time? time_zone?) param_pair*
        debit:  _DEBIT_SIGN  (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        credit: _CREDIT_SIGN (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        entry_footer: _ENTRY_END_MARK
        """
    csv_def_str = r'''    
        start: header _NL row+
        header: ("\"" [STRING_AND_MARK] "\"" _SEPARATOR?)+
        row: ("\"" [contents tekiyou contents] "\"" _SEPARATOR?)+ _NL
        _SEPARATOR: ","
        contents: STRING_AND_MARK2?
    
        %import common.NEWLINE -> _NL
        %ignore WS3
        '''
    default_mf_csv_filename="仕訳データ.csv"

    def __init__(self):
        pass
        ## ver20230610
        #self.lark_def_str = QTYJournalToTree().get_lark_def_str()
        #self.datetime_def_str =QTYJournalToTree().datetime_def_str
        #self.tekiyou_parser_lalr = Lark(self.tekiyou_def_str+QTYJournalToTree.lark_def_str+QTYJournalToTree.datetime_def_str,start ="tekiyou",parser='lalr')
        self.csv_parser_mf_lalr = Lark(self.csv_def_str+self.tekiyou_def_str+QTYJournalToTree.lark_def_str+QTYJournalToTree.datetime_def_str,start ="start",parser='lalr',maybe_placeholders=True)

    def translate_file(self,filename=None):
        if filename is None:
            filename = os.path.join(Path().resolve(), self.default_mf_csv_filename)
    
        #with open(filename, 'r', newline=None, encoding='utf-8') as f:
        with open(filename, 'r', newline=None, encoding='shift_jis') as f:
            csv_tree = self.csv_parser_mf_lalr.parse(f.read())
    
        return csv_tree
    
    def translate(self,csv_text):
        return self.csv_parser_mf_lalr.parse(csv_text)
    

class  CSVTreeToJournalDic(InterpretBaseTree):
    
    def __init__(self):
        self.csv_header =[]
        
    def get_journal_text(self,csv_tree):
        journal_dic = self.visit(csv_tree)
        journal_text = JournalDicToText().get_text_from_journal_dic(journal_dic)
        return journal_text
    
    def get_heading(self,index):
        if index < len(self.csv_header):
            return self.csv_header[index]
        return None
    
    
    def mearge_entry_dic(self,entry_dic,row_dic):
        #entry_dicを書き換える可能性
        #entry_dic
        #{"entry_header":{"entry_id":None},"body":[],"entry_footer":{}}
        #row_dic
        #{"entry_header":{"entry_id":None},"body":[],"entry_footer":{}}
        entry_dic_header = entry_dic["entry_header"]
        row_dic_header = row_dic.get("entry_header",None)
        #entry_header
        if row_dic_header is None:
            return entry_dic
        
        entry_dic_header_memo_org = entry_dic_header.get("memo",None)
        entry_dic["entry_header"].update(row_dic_header)
        
        if entry_dic_header_memo_org is not None:
            if entry_dic["entry_header"].get("memo",None) is not None:
                entry_dic["entry_header"]["memo"].update(entry_dic_header_memo_org)        
        
        #body
        # row_dicの Dr Crをentry_dicに追加する
        row_dic_dr = row_dic["body"][0]
        #勘定科目の指定があるもののみを追加する
        if row_dic_dr["debit"]["account"] is not None:
            entry_dic["body"].append(row_dic_dr)
       #Cr
        row_dic_cr = row_dic["body"][1]
        #勘定科目の指定があるもののみを追加する
        if row_dic_cr["credit"]["account"] is not None:
            entry_dic["body"].append(row_dic_cr)
            
        return entry_dic
    def mearge_tekiyou(self,row_dic,tekiyou):
        #tekiyou 
        # {'tekiyou_entry': 
        #  {'entry_header': 
        #   {'partner': '得意先あ', 'person_in_charge': 'ken', 'memo': {'温度': (23, None)}, 'remarks': 'test1'},
        #  'body': [
        #   {'debit': {'item': '0901234567', 'quantity': 10, 'quantity_unit': '個', 'amount': 100000.12, 'amount_unit': '円', 'memo': {'メッセージ': 'こんにちは', '気温': (24, None)}, 'remarks': 'test2'}},
        #   {'credit': {}}],
        #  'entry_footer': 
        #row_dic
        #{"entry_header":{"entry_id":None},"body":[],"entry_footer":{}}
        row_dic_entry_header = row_dic["entry_header"]
        if tekiyou.get("tekiyou_entry",None) is None:
            return row_dic
        tekiyou_entry_header = tekiyou["tekiyou_entry"].get("entry_header",None)

        #entry_header
        if tekiyou_entry_header is None:
            return row_dic
        row_dic_header_memo_org = row_dic_entry_header.get("memo",None)
        row_dic["entry_header"].update(tekiyou_entry_header)
        if row_dic_header_memo_org is not None:
            if row_dic["entry_header"].get("memo",None) is not None:
                row_dic["entry_header"]["memo"].update(row_dic_header_memo_org)
        #datetime
        #MFでは時刻以下は指定されない追加する
        datetime_str = row_dic["entry_header"]["datetime"]
        date_str = datetime_str.split("T")[0]
        prefixed_time_str=  row_dic["entry_header"].get("prefixed_time","")
        time_zone_str = row_dic["entry_header"].get("time_zone","")
        
        row_dic["entry_header"]["datetime"]=date_str+prefixed_time_str+time_zone_str
        
        #body
        # row_dic のDr Cr に　tekiyouのパラメータを反映する
        #Dr
        row_dic_dr = row_dic["body"][0].get("debit",None)
        if row_dic_dr is not None:
            tekiyou_dr = tekiyou["tekiyou_entry"]["body"][0].get("debit",None)
            if tekiyou_dr is not None:
                row_dic_dr_memo_org = row_dic_dr.get("memo",None)

                #tekiyou_drでamountを指定した場合、updateされる。
                #もとの会計ファイルで指定していたamountが上書きされるので、
                #それが必要な場合は、debitのメモORIGINAL_AMOUNTに保存されている値を参照する
                row_dic["body"][0]["debit"].update(tekiyou_dr)

                if row_dic_dr_memo_org is not None:
                    if row_dic["body"][0].get("memo",None) is not None:
                        row_dic["body"][0]["memo"].update(row_dic_dr_memo_org)

        #Cr
        row_dic_cr = row_dic["body"][1].get("credit",None)
        if row_dic_cr is not None:
            tekiyou_cr = tekiyou["tekiyou_entry"]["body"][1].get("credit",None)
            if tekiyou_cr is not None:
                row_dic_cr_memo_org = row_dic_cr.get("memo",None)

                #tekiyou_crでamountを指定した場合、updateされる。
                #もとの会計ファイルで指定していたamountが上書きされるので、
                #それが必要な場合は、creditのメモORIGINAL_AMOUNTに保存されている値を参照する
                row_dic["body"][1]["credit"].update(tekiyou_cr)
                if row_dic_cr_memo_org is not None:
                    if row_dic["body"][1].get("memo",None) is not None:
                        row_dic["body"][1]["memo"].update(row_dic_cr_memo_org)

        return row_dic
    
    def safe_trans(self,texts):
        #safe_dic={'/': '_'}
        safe_dic={'/': '_',' ':'_',':':'_','　':'_','%':'_PCT_','-':'_',',':'_'}
        return texts.translate(str.maketrans(safe_dic))
        
    def start(self,tree):
        #start: header _NL row+
        data =[]
        #header
        self.csv_header = self.visit(tree.children[0])

        #row
        last_entry_id=None
        entry_dic = {"entry_header":{"entry_id":None},"body":[],"entry_footer":{}}
        something_in_entry_dic = False
        
        for c in tree.children[1:]:
            row_dic = self.visit(c)
            #print(row_dic)
            entry_id = row_dic["entry_header"]["entry_id"]
            if entry_id is None:
                #print("entry_id is None")
                continue

            if (last_entry_id is not None) and (last_entry_id != entry_id):
                #Flush
                #print("entry_dic at flush",entry_dic)
                data.append({"journal_entry":entry_dic})
                entry_dic = {"entry_header":{"entry_id":None},"body":[],"entry_footer":{}}
                something_in_entry_dic = False
                
            entry_dic = self.mearge_entry_dic(entry_dic,row_dic)
            something_in_entry_dic = True                
            last_entry_id = entry_id
                
        if something_in_entry_dic:
            data.append({"journal_entry":entry_dic})
            
        return {"journal":data}
        
    def header(self,tree):
        header = [c.value for c in tree.children]
        #header: ("\"" [STRING_AND_MARK] "\"" _SEPARATOR?)+
        return header
        
    def row(self,tree):
        #row: ("\"" [contents tekiyou contents] "\"" _SEPARATOR?)+ _NL
        row_dic = {"entry_header":{"entry_id":None,"datetime":None,"memo":{}},"body":[{"debit":{"account":None,"sub_account":None,"amount":None,"memo":{}}},{"credit":{"account":None,"sub_account":None,"amount":None,"memo":{}}}],"entry_footer":{}}
        num_heading = len(tree.children) // 3
        #print("num_heading",num_heading)
        for i in range(0,num_heading):
            c0 = tree.children[i*3]
            assert c0 is None or c0.data=="contents"
            c1 =  tree.children[i*3+1]
            assert c1 is None or c1.data=="tekiyou"
            c2 =  tree.children[i*3+2]
            assert c2 is None or c2.data=="contents"
            heading = self.get_heading(i)
            #print()
            if heading=="取引No":
                assert i == 0
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["entry_header"]["entry_id"]=content
                    row_dic["entry_header"]["memo"]["取引No"]=content
            elif heading=="取引日":
                assert i == 1
                if c0 is not None:
                    #print("c0",c0)
                    content = self.visit(c0)
                    #print("content",content)
                    datetime_str = content.replace('/', '-')
                    row_dic["entry_header"]["datetime"]=datetime_str
            elif heading=="借方勘定科目":
                assert i == 2
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["body"][0]["debit"]["account"]=content
            elif heading=="借方補助科目":
                assert i == 3
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["body"][0]["debit"]["sub_account"]=content
            elif heading=="借方部門":
                assert i == 4
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][0]["debit"]["memo"]["借方部門"]=content
            elif heading=="借方取引先":
                assert i == 5
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][0]["debit"]["partner"]=content
            elif heading=="借方税区分":
                assert i == 6
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][0]["debit"]["memo"]["借方税区分"]=content
            elif heading=="借方インボイス":
                assert i == 7
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][0]["debit"]["memo"]["借方インボイス"]=content
            elif heading=="借方金額(円)":
                assert i == 8
                if c0 is not None:
                    content = self.visit(c0)
                    if "." in content:
                        contnt_number = float(content)
                    else:
                        contnt_number = int(content)
                    row_dic["body"][0]["debit"]["amount"]=contnt_number
                    #ORIGINAL_AMOUNT ORIGINAL_AMOUNT_UNIT
                    # todo
                    row_dic["body"][0]["debit"]["memo"]["ORIGINAL_AMOUNT"]=contnt_number
                    row_dic["body"][0]["debit"]["memo"]["ORIGINAL_AMOUNT_UNIT"]="円"
                    #row_dic["body"][0]["debit"]["memo"]["ORIGINAL_AMOUNT"]=(contnt_number,"円")
            elif heading=="借方税額":
                assert i == 9
                if c0 is not None:
                    content = self.visit(c0)
                    content_int = int(content)
                    row_dic["body"][0]["debit"]["memo"]["借方税額"]=content_int
                    row_dic["body"][0]["debit"]["memo"]["借方税額単位"]="円"             
            elif heading=="貸方勘定科目":
                assert i == 10
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["body"][1]["credit"]["account"]=content
            elif heading=="貸方補助科目":
                assert i == 11
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["body"][1]["credit"]["sub_account"]=content
            elif heading=="貸方部門":
                assert i == 12
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][1]["credit"]["memo"]["貸方部門"]=content
            elif heading=="貸方取引先":
                assert i == 13
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["body"][1]["credit"]["partner"]=content
            elif heading=="貸方税区分":
                assert i == 14
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][1]["credit"]["memo"]["貸方税区分"]=content
            elif heading=="貸方インボイス":
                assert i == 15
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["body"][0]["debit"]["memo"]["貸方インボイス"]=content
            elif heading=="貸方金額(円)":
                assert i == 16
                if c0 is not None:
                    content = self.visit(c0)
                    if "." in content:
                        contnt_number = float(content)
                    else:
                        contnt_number = int(content)
                    row_dic["body"][1]["credit"]["amount"]=contnt_number
                    #ORIGINAL_AMOUNT ORIGINAL_AMOUNT_UNIT
                    row_dic["body"][1]["credit"]["memo"]["ORIGINAL_AMOUNT"]=contnt_number
                    row_dic["body"][1]["credit"]["memo"]["ORIGINAL_AMOUNT_UNIT"]="円"

            elif heading=="貸方税額":
                assert i == 17
                if c0 is not None:
                    content = self.visit(c0)
                    content_int = int(content)
                    row_dic["body"][1]["credit"]["memo"]["貸方税額"]=content_int
                    row_dic["body"][1]["credit"]["memo"]["貸方税額単位"]="円"

            elif heading=="摘要":
                assert i == 18
                remarks =""
                if c0 is not None:
                    remarks0 = self.visit(c0)
                    if remarks0 is not None:
                        remarks += remarks0

                if c1 is not None:    
                    tekiyou = self.visit(c1)
                    if tekiyou is not None:
                        #print("tekiyou",tekiyou)
                        row_dic= self.mearge_tekiyou(row_dic,tekiyou)
                        
                if c2 is not None:            
                    remarks2 = self.visit(c2)
                    if remarks2 is not None:
                        remarks += remarks2
                remarks = self.safe_trans(remarks)        
                row_dic["body"][0]["debit"]["remarks"]=remarks
                row_dic["body"][1]["credit"]["remarks"]=remarks
                #print("row_dic",row_dic)
                
            elif heading=="仕訳メモ":
                assert i == 19
                #仕訳メモ は仕訳全体に対するものだが、各行に同じ内容が記載される
                remarks =""
                if c0 is not None:
                    remarks0 = self.visit(c0)
                    if remarks0 is not None:
                        remarks += remarks0

                if c1 is not None:    
                    tekiyou = self.visit(c1)
                    if tekiyou is not None:
                        #print("tekiyou",tekiyou)
                        row_dic= self.mearge_tekiyou(row_dic,tekiyou)
                        
                if c2 is not None:            
                    remarks2 = self.visit(c2)
                    if remarks2 is not None:
                        remarks += remarks2
                        
                remarks = self.safe_trans(remarks)        
                row_dic["entry_header"]["remarks"]=remarks
                
            elif heading=="タグ":
                assert i == 20
                #タグ は仕訳全体に対するものだが、各行に同じ内容が記載される
                #タグがある場合は、キーがタグ名のメモを作成し、値を"1"とする。
                if c0 is not None:
                    content = self.visit(c0)
                    if content is not None and len(content)>0:
                        tags = content.split("|")
                        for tag in tags:
                            row_dic["entry_header"]["memo"][tag]="1"
                pass
            elif heading=="MF仕訳タイプ":
                assert i == 21
                if c0 is not None:
                    content = self.visit(c0)
                    if content=="開始仕訳":
                        row_dic["entry_header"]["memo"]["KIND"]="OPENING"
            elif heading=="決算整理仕訳":
                assert i == 22
                if c0 is not None:
                    content = self.visit(c0)
                    if content=="1":
                        row_dic["entry_header"]["memo"]["KIND"]="ADJUSTING"
            elif heading=="作成日時":
                assert i == 23
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["entry_header"]["memo"]["作成日時"]=content
            elif heading=="作成者":
                assert i == 24
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["entry_header"]["memo"]["作成者"]=content
            elif heading=="最終更新日時":
                assert i == 25
                if c0 is not None:
                    content = self.visit(c0)
                    content = self.safe_trans(content)
                    row_dic["entry_header"]["memo"]["最終更新日時"]=content
            elif heading=="最終更新者":
                assert i == 26
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["entry_header"]["memo"]["最終更新者"]=content
            else:
                if c0 is not None:
                    content = self.visit(c0)
                    row_dic["entry_header"]["memo"][heading]=content
        #print(row_dic)
        return row_dic
    
    def tekiyou(self,tree):
        #tekiyou: tekiyou_entry?
        #tekiyou_entry: entry_header (debit | credit)+ entry_footer
        #entry_header: _ENTRY_START_MARK (prefixed_time? time_zone?) param_pair*
        #debit:  _DEBIT_SIGN  (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        #credit: _CREDIT_SIGN (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        #entry_footer: _ENTRY_END_MARK

        #journal_entry: entry_header (debit | credit)* entry_footer
        #entry_header: _ENTRY_START_MARK  datetime param_pair*
        #debit: journal_entry _DEBIT_SIGN   account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        #credit: _CREDIT_SIGN  account (_SUB_ACCOUNT_MARK sub_account)? (_ITEM_MARK item)? (_PRICE_MARK price)? (_QUANTITY_MARK quantity quantity_unit)? (amount? amount_unit?) param_pair*
        #entry_footer: _ENTRY_END_MARK
        
        #違い　
        #header　datetime　vs (prefixed_time? time_zone?)
        #debit/credit  account (_SUB_ACCOUNT_MARK sub_account)? vs なし
        #              (amount? amount_unit?)   vs  別途金額指定＋(amount? amount_unit?) 

        #対応
        #・(prefixed_time? time_zone?)の指定がある場合には追加
        #・account sub_account は会計ファイルのものを追加
        #・(amount? amount_unit?)　の指定がある場合は、そちらを優先し、
        #・会計ファイル記載の金額は、メモ&ORIGINAL_AMOUNT:金額　に残しておく　→別途差額の仕訳を出力できる
        #  ない場合は、会計ファイルの金額を使う
        #・debit_info/credit_info の表現はそのまま使える。ただし、
        # account sub_accountを左に追加
        #・(amount? amount_unit?)の指定がある場合　メモ&ORIGINAL_AMOUNT:金額に元の金額を残す
        #・(amount? amount_unit?)の指定がない場合　金額をその部分に挿入
        # (prefixed_time? time_zone?)の指定がある場合には会計ファイルの日付に追加
        # datetime を左に追加
        # 同じ仕訳の中で、日付や時刻が異なる場合には、最初に明示的に指定したものとする（同一仕訳同一時刻）
        # 開始仕訳 決算整理仕訳 はheaderで指定。最初に明示的に指定したものとする。
        tekiyou = {"tekiyou_entry":None}
        if len(tree.children)>0:
            tekiyou["tekiyou_entry"] = self.visit(tree.children[0])
            #print("tekiyou",tekiyou)
        return tekiyou

    def tekiyou_entry(self,tree):
        #tekiyou_entry: entry_header (debit | credit)+ entry_footer
        tekiyou_entry ={"entry_header":None,"body":[{"debit":{}},{"credit":{}}],"entry_footer":None}
        for c in tree.children:
            if c.data == "entry_header":
                entry_header = self.visit(c)
                tekiyou_entry["entry_header"]=entry_header
            elif c.data == "debit":
                debit = self.visit(c)
                tekiyou_entry["body"][0]["debit"].update(debit)
            elif c.data == "credit":
                credit = self.visit(c)
                tekiyou_entry["body"][1]["credit"].update(credit)              
            elif c.data == "entry_footer":
                entry_footer = self.visit(c)
                tekiyou_entry["entry_footer"]=entry_footer
        return tekiyou_entry
        
    def prefixed_time(self,tree):
        #prefixed_time: PREFIXED_TIME
        return tree.children[0].value
    
    def time_zone(self,tree):
        #time_zone: TIME_ZONE
        return tree.children[0].value
    
    def contents(self,tree):
        #contents: STRING_AND_MARK2?
        if len(tree.children)==0:
            return ""
        return tree.children[0].value

def main():
    #sample_file_name = "mfsample.csv"
    #file_path  = os.path.join(Path().resolve(), sample_file_name)
    target_path_2 = os.path.join(os.path.dirname(__file__), '../example/mfsample.csv')
    file_path = os.path.normpath(target_path_2)
    csv_tree = MfCSVToCSVTree().translate_file(file_path)

    #csv_tree　-> journal_dic  -> ledgers
    journal_dic = CSVTreeToJournalDic().visit(csv_tree)
    #print(journal_dic)
    journal_tree = QTYJournalDicToTree().translate(journal_dic)
    print(journal_tree)

    #csv_tree　-> journal_text  -> ledgers
    #journal_text = CSVTreeToJournalDic().get_journal_text(csv_tree)
    #print(journal_text)
    #journal_tree = QTYJournalToTree().translate(journal_text)

    ledgers =InterpretJournalTree().get_ledgers(journal_tree)
    #df = ledgers.simple_ledger_to_df("商品","","Tシャツ")
    #print(df)
    #ledgers.simple_ledger_to_excel("商品","","Tシャツ")
    df_tb = ledgers.tb_to_df(start_datetime="2022-05-01",end_datetime="2023-01-01")
    ledgers.tb_to_excel(start_datetime="2022-05-01",end_datetime="2023-01-01")

if __name__ == "__main__":
    main()