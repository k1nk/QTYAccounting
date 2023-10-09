import pytest
import os
from qtyaccounting.mftools import MfCSVToCSVTree,CSVTreeToJournalDic
from lark import Tree,Token

def test_translate():
    csv_text = r'''"取引No","取引日","借方勘定科目","借方補助科目","借方部門","借方取引先","借方税区分","借方インボイス","借方金額(円)","借方税額","貸方勘定科目","貸方補助科目","貸方部門","貸方取引先","貸方税区分","貸方インボイス","貸方金額(円)","貸方税額","摘要","仕訳メモ","タグ","MF仕訳タイプ","決算整理仕訳","作成日時","作成者","最終更新日時","最終更新者"
"1","2023/04/01","普通預金","","","","対象外","","93000","0","資本金","","","","対象外","","100000","0","","","","開始仕訳","","","中谷 賢一","","中谷 賢一"
"1","2023/04/01","商品","","","","対象外","","7000","0","","","","","","","0","0","<<Dr #Tシャツ *10個>>","","","開始仕訳","","","中谷 賢一","","中谷 賢一"
"2","2023/08/01","商品","","","","対象外","","6000","0","普通預金","","","","対象外","","6000","0","<<Dr #Tシャツ *10個>>","","","","","2023/8/1 23:02:23","中谷 賢一","2023/8/1 23:04:10","中谷 賢一"
"3","2023/08/02","商品","","","","対象外","","7000","0","普通預金","","","","対象外","","7000","0","<<Dr #Tシャツ *10個>>","","","","","2023/8/1 23:03:42","中谷 賢一","2023/8/1 23:04:23","中谷 賢一"
"4","2023/08/03","仕入高","","","","課税仕入 10%","","1","0","商品","","","","対象外","","1","0","<<Dr #Tシャツ　?E個  $得意先A Cr #Tシャツ　*5個 ? >>","","","","","2023/8/1 23:11:46","中谷 賢一","2023/8/1 23:12:55","中谷 賢一"
"4","2023/08/03","売掛金","","","","対象外","","1","0","売上高","","","","課税売上 10%","","1","0","<<Dr ?E Cr #Tシャツ @200 *5個 &天気::晴れ &気温:26度　##売上計上>>","","","","","","中谷 賢一","","中谷 賢一"
'''
    csv_tree = MfCSVToCSVTree().translate(csv_text)
    assert csv_tree.data==Token('RULE', 'start'),"startが解析されているか"
    header = csv_tree.children[0]
    assert header.data==Token('RULE', 'header'),"headerが解析されているか"
    row = csv_tree.children[1]
    assert row.data==Token('RULE', 'row'),"rowが解析されているか"

def test_translate_file():
    target_path_2 = os.path.join(os.path.dirname(__file__), '../example/mfsample.csv')
    file_path = os.path.normpath(target_path_2)
    csv_tree = MfCSVToCSVTree().translate_file(file_path)
    assert csv_tree.data==Token('RULE', 'start'),"startが解析されているか"
    header = csv_tree.children[0]
    assert header.data==Token('RULE', 'header'),"headerが解析されているか"
    row = csv_tree.children[1]
    assert row.data==Token('RULE', 'row'),"rowが解析されているか"

#def test_visit()
#    journal_dic = CSVTreeToJournalDic().visit(csv_tree)
