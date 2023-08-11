import pytest
from qtyaccounting.qtytools import QTYJournalToTree
from lark import Tree,Token

def test_translate():
    journal1 = r"""
<<2022-05-14 ##商品の仕入１
Dr　商品#Tシャツ *10個 6000円
Cr　預金 6000>>"""
    tree1 = QTYJournalToTree().translate(journal1)
    assert tree1.data==Token('RULE', 'journal'),"journalが解析されているか"
    jourrnal_entry = tree1.children[0]
    assert jourrnal_entry.data==Token('RULE', 'journal_entry'),"journal_entryが解析されているか"
    entry_header = jourrnal_entry.children[0]
    assert entry_header.data==Token('RULE', 'entry_header'),"entry_headerが解析されているか"
    debit = jourrnal_entry.children[1]
    assert debit.data==Token('RULE', 'debit'),"debitが解析されているか"
    credit = jourrnal_entry.children[2]
    assert credit.data==Token('RULE', 'credit'),"creditが解析されているか"
    entry_footer = jourrnal_entry.children[3]
    assert entry_footer.data==Token('RULE', 'entry_footer'),"entry_footerが解析されているか"    

def test_datetime():
    journal1 = r"""
<<2023-08-07T03:12:40+09:00 ##商品の仕入１
Dr　商品#Tシャツ *10個 6000円
Cr　預金 6000>>"""
    tree1 = QTYJournalToTree().translate(journal1)
    jourrnal_entry = tree1.children[0]
    entry_header = jourrnal_entry.children[0]
    datetime = entry_header.children[0]
    assert datetime.data==Token('RULE', 'datetime'),"datetimeが解析されているか"
    assert datetime.children[0]==Token('DATETIME', '2023-08-07T03:12:40+09:00'),"datetimeの内容が取得されているか"

def test_header_remarks():
    #remarksのテスト
    journal1 = r"""
<<2023-08-07T03:12:40+09:00 ##商品の仕入１
Dr　商品#Tシャツ *10個 6000円
Cr　預金 6000>>"""
    tree1 = QTYJournalToTree().translate(journal1)
    jourrnal_entry = tree1.children[0]
    entry_header = jourrnal_entry.children[0]
    param_pair = entry_header.children[1]
    assert param_pair.data==Token('RULE', 'param_pair'),"param_pairが解析されているか"
    param_mark = param_pair.children[0]
    assert param_mark.data==Token('RULE', 'param_mark'),"param_markが解析されているか"
    assert param_mark.children[0]==Token('REMARKS_MARK', '##'),"param_markの内容が解析されているか"
    param = param_pair.children[1]
    assert param.data==Token('RULE', 'param'),"paramが解析されているか"
    string = param.children[0]
    assert string.data==Token('RULE', 'string'),"stringが解析されているか"
    assert string.children[0]==Token('STRING', '商品の仕入１'),"stringの内容が解析されているか"



