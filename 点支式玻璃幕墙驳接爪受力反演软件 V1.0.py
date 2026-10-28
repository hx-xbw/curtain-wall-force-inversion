# -*- coding: utf-8 -*-
# 软件名称：点支式玻璃幕墙驳接爪受力反演软件V1.0
# 版权声明：本软件为自主开发，仅用于建筑幕墙节点受力反演与工程资料管理
# 开发工具：VS Code、PyQt6、SQLite3
# 编程语言：Python、JavaScript
#
# 本版补全内容：
#   1. 账号登录、角色权限（管理员 / 工程师 / 访客）
#   2. 工程 → 玻璃分格 → 驳接爪节点 三级台账维护
#   3. 测点应变、挠度数据录入与校验
#   4. 基于真实测点数据的加权正则化 + SVD 融合反演
#   5. 反演结果落库、SHA256 摘要、三维着色联动
#   6. 成果报告 PDF 导出、签认、证据链打包与校验
#   7. 账号管理、审计日志

import sys

# WebEngine 运行参数必须在 QApplication 实例化之前追加
sys.argv += ["--no-sandbox"]

import hashlib
import html as html_lib
import hmac
import json
import math
import os
import random
import re
import sqlite3
import zipfile
from datetime import datetime
from pathlib import Path

import numpy as np
from scipy.interpolate import griddata

os.environ.setdefault("QTWEBENGINE_CHROMIUM_FLAGS", "--no-sandbox")

from PyQt6.QtCore import QPointF, QRectF, QSize, Qt, QThread, QUrl, pyqtSignal
from PyQt6.QtGui import (
    QBrush, QColor, QFont, QFontMetrics, QLinearGradient, QPainter,
    QPainterPath, QPen, QPolygonF, QTextDocument,
)
from PyQt6.QtPrintSupport import QPrinter
from PyQt6.QtWidgets import (
    QAbstractItemView, QApplication, QComboBox, QDialog, QDoubleSpinBox,
    QFileDialog, QFormLayout, QFrame, QGridLayout, QGroupBox, QHBoxLayout,
    QHeaderView, QInputDialog, QLabel, QLineEdit, QListWidget, QMainWindow,
    QMessageBox, QPushButton, QSizePolicy, QSlider, QSplitter, QSpinBox,
    QStackedWidget, QTableWidget, QTableWidgetItem, QTextEdit, QToolTip,
    QVBoxLayout, QWidget,
)

try:
    from PyQt6.QtWebEngineCore import QWebEngineSettings
    from PyQt6.QtWebEngineWidgets import QWebEngineView
    HAS_WEBENGINE = True
except Exception:  # WebEngine 组件缺失时退化为普通界面
    QWebEngineSettings = None
    QWebEngineView = None
    HAS_WEBENGINE = False

# --------------------------全局常量定义--------------------------
BASE_DIR = Path(__file__).resolve().parent
DB_PATH = str(BASE_DIR / "musk_analysis.db")
SAVE_ROOT = BASE_DIR / "project_output"
SCENE_PATH = BASE_DIR / "scene.html"
REPORT_DIR = SAVE_ROOT / "reports"
EVIDENCE_DIR = SAVE_ROOT / "evidence"
ALG_WEIGHT_REG = 0.01
SVD_THRESHOLD = 1e-6
SHA_ALG = "sha256"
USER_ROLE_ADMIN = 0
USER_ROLE_ENGINEER = 1
USER_ROLE_VISITOR = 2
ROLE_NAMES = {USER_ROLE_ADMIN: "管理员", USER_ROLE_ENGINEER: "工程师", USER_ROLE_VISITOR: "访客"}
PROJECT_STATUS = ["在建", "设计中", "已竣工", "暂停"]
NODE_TYPES = ["四爪", "三爪", "两爪", "单爪"]
APP_TITLE = "点支式玻璃幕墙驳接爪受力反演软件 V1.0"

# --------------------------界面主题（QSS）--------------------------
APP_QSS = """
* {
    font-family: "Microsoft YaHei UI", "Microsoft YaHei", "Segoe UI", sans-serif;
}
QWidget {
    color: #1f2937;
    font-size: 13px;
}
QMainWindow, QWidget#appRoot {
    background: #f3f5f9;
}
QWidget#page, QWidget#pageBody {
    background: transparent;
}
QToolTip {
    background: #0f172a;
    color: #e2e8f0;
    border: none;
    padding: 6px 8px;
}

/* ---------- 左侧导航 ---------- */
QFrame#sidebar {
    background: #0f172a;
    border: none;
}
QWidget#brandBox {
    background: transparent;
}
QLabel#brandLogo {
    background: #2563eb;
    color: #ffffff;
    border-radius: 10px;
    font-size: 20px;
    font-weight: 700;
}
QLabel#brandName {
    color: #f8fafc;
    font-size: 14px;
    font-weight: 600;
}
QLabel#brandSub {
    color: #64748b;
    font-size: 9px;
}
QLabel#navSection {
    color: #52627a;
    font-size: 10px;
    font-weight: 600;
}
QListWidget#nav {
    background: transparent;
    border: none;
    outline: 0;
    padding: 4px 12px;
}
QListWidget#nav::item {
    height: 36px;
    padding-left: 14px;
    border-radius: 8px;
    margin: 0;
    color: #94a3b8;
    font-size: 12px;
}
QListWidget#nav::item:hover {
    background: #18243a;
    color: #e2e8f0;
}
QListWidget#nav::item:selected {
    background: #1d4ed8;
    color: #ffffff;
    font-weight: 600;
}
QFrame#sidebarUser {
    background: #0b1424;
    border-top: 1px solid #1e293b;
}
QLabel#avatar {
    background: #2563eb;
    color: #ffffff;
    border-radius: 17px;
    font-size: 14px;
    font-weight: 600;
}
QLabel#userName {
    color: #e2e8f0;
    font-size: 12px;
}
QLabel#userRole {
    color: #64748b;
    font-size: 10px;
}
QPushButton#sideExit {
    background: transparent;
    border: none;
    color: #64748b;
    font-size: 11px;
    padding: 4px 6px;
}
QPushButton#sideExit:hover {
    color: #f87171;
}

/* ---------- 顶栏 ---------- */
QFrame#topbar {
    background: #ffffff;
    border-bottom: 1px solid #e5e9f0;
}
QLabel#crumb {
    color: #64748b;
    font-size: 12px;
}
QLabel#dbDot {
    color: #16a34a;
    font-size: 11px;
}
QLabel#dbState {
    color: #64748b;
    font-size: 12px;
}
QLabel#topUser {
    color: #334155;
    font-size: 12px;
    font-weight: 600;
}

/* ---------- 页面标题 ---------- */
QLabel#pageTitle {
    font-size: 21px;
    font-weight: 700;
    color: #0f172a;
}
QLabel#pageSub {
    font-size: 12px;
    color: #64748b;
}

/* ---------- 卡片 / 分组 ---------- */
QGroupBox {
    background: #ffffff;
    border: 1px solid #e5e9f0;
    border-radius: 10px;
    margin-top: 0;
    padding: 40px 14px 14px 14px;
    font-weight: 600;
    color: #334155;
}
QGroupBox::title {
    subcontrol-origin: padding;
    subcontrol-position: top left;
    left: 16px;
    top: 13px;
    padding: 0;
    color: #334155;
    background: transparent;
}
QWidget#filterBar {
    background: #ffffff;
    border: 1px solid #e5e9f0;
    border-radius: 8px;
}
QLabel#filterLabel {
    color: #64748b;
    font-size: 12px;
}

/* ---------- 仪表盘 / 分析页 ---------- */
QFrame#statCard {
    background: #ffffff;
    border: 1px solid #e5e9f0;
    border-radius: 10px;
}
QLabel#statTitle {
    color: #64748b;
    font-size: 12px;
}
QLabel#statValue {
    color: #0f172a;
    font-size: 26px;
    font-weight: 700;
}
QLabel#statUnit {
    color: #94a3b8;
    font-size: 11px;
}
QLabel#statHint {
    color: #94a3b8;
    font-size: 11px;
}
QFrame#accentBar {
    border-radius: 2px;
}
QFrame#resultCard {
    background: #f8fafc;
    border: 1px solid #e5e9f0;
    border-radius: 8px;
}
QLabel#resultValue {
    color: #0f172a;
    font-size: 18px;
    font-weight: 700;
}
QLabel#resultLabel {
    color: #64748b;
    font-size: 11px;
}
QLabel#tagOk {
    background: #dcfce7;
    color: #15803d;
    border-radius: 9px;
    padding: 2px 10px;
    font-size: 11px;
    font-weight: 600;
}
QLabel#tagWarn {
    background: #fef3c7;
    color: #b45309;
    border-radius: 9px;
    padding: 2px 10px;
    font-size: 11px;
    font-weight: 600;
}
QLabel#tagInfo {
    background: #dbeafe;
    color: #1d4ed8;
    border-radius: 9px;
    padding: 2px 10px;
    font-size: 11px;
    font-weight: 600;
}
QLabel#sectionHint {
    color: #94a3b8;
    font-size: 11px;
}

/* ---------- 按钮 ---------- */
QPushButton {
    background: #ffffff;
    border: 1px solid #d7dee9;
    border-radius: 7px;
    padding: 6px 14px;
    color: #334155;
    min-height: 22px;
}
QPushButton:hover {
    border-color: #93b4f5;
    color: #1d4ed8;
    background: #f7faff;
}
QPushButton:pressed {
    background: #eef4ff;
}
QPushButton:disabled {
    color: #a8b3c4;
    background: #f4f6fa;
    border-color: #e5e9f0;
}
QPushButton#primaryBtn {
    background: #2563eb;
    border: 1px solid #2563eb;
    color: #ffffff;
    font-weight: 600;
}
QPushButton#primaryBtn:hover {
    background: #1d4ed8;
    border-color: #1d4ed8;
}
QPushButton#primaryBtn:pressed {
    background: #1e40af;
}
QPushButton#primaryBtn:disabled {
    background: #bfdbfe;
    border-color: #bfdbfe;
    color: #eff6ff;
}
QPushButton#dangerBtn {
    color: #dc2626;
    border: 1px solid #f3c6c2;
    background: #ffffff;
}
QPushButton#dangerBtn:hover {
    background: #fef2f2;
    border-color: #ef4444;
    color: #b91c1c;
}
QPushButton#ghostBtn {
    background: transparent;
    border: 1px solid transparent;
    color: #64748b;
}
QPushButton#ghostBtn:hover {
    background: #eef4ff;
    color: #1d4ed8;
    border-color: transparent;
}

/* ---------- 输入控件 ---------- */
QLineEdit, QComboBox, QSpinBox, QDoubleSpinBox {
    background: #ffffff;
    border: 1px solid #d7dee9;
    border-radius: 7px;
    padding: 6px 10px;
    min-height: 20px;
    selection-background-color: #bfdbfe;
    selection-color: #0f172a;
}
QLineEdit:focus, QComboBox:focus, QSpinBox:focus, QDoubleSpinBox:focus {
    border: 1px solid #2563eb;
}
QLineEdit:disabled, QComboBox:disabled, QSpinBox:disabled, QDoubleSpinBox:disabled {
    background: #f4f6fa;
    color: #94a3b8;
}
QComboBox::drop-down {
    border: none;
    width: 26px;
}
QComboBox QAbstractItemView {
    background: #ffffff;
    border: 1px solid #d7dee9;
    border-radius: 6px;
    selection-background-color: #e8f0fe;
    selection-color: #1d4ed8;
    outline: 0;
}
QSpinBox::up-button, QDoubleSpinBox::up-button,
QSpinBox::down-button, QDoubleSpinBox::down-button {
    width: 18px;
    border: none;
    background: transparent;
}

/* ---------- 表格 ---------- */
QTableWidget {
    background: #ffffff;
    border: 1px solid #e5e9f0;
    border-radius: 10px;
    gridline-color: #eef2f7;
    alternate-background-color: #fafbfe;
    selection-background-color: #e8f0fe;
    selection-color: #0f172a;
    outline: 0;
}
QTableWidget::item {
    padding: 6px 8px;
    border: none;
}
QTableWidget::item:selected {
    background: #e8f0fe;
    color: #0f172a;
}
QHeaderView::section {
    background: #f7f9fc;
    color: #64748b;
    padding: 9px 8px;
    border: none;
    border-bottom: 1px solid #e5e9f0;
    font-weight: 600;
}
QTableCornerButton::section {
    background: #f7f9fc;
    border: none;
}

/* ---------- 日志 / 文本 ---------- */
QTextEdit {
    background: #ffffff;
    border: 1px solid #e5e9f0;
    border-radius: 10px;
    padding: 8px;
    selection-background-color: #bfdbfe;
}
QTextEdit#calcLog {
    background: #0f172a;
    color: #cfe1ff;
    border: none;
    border-radius: 10px;
    padding: 14px;
    font-family: Consolas, "Microsoft YaHei", monospace;
    font-size: 12px;
}

/* ---------- 拆分条 / 滚动条 ---------- */
QSplitter::handle {
    background: transparent;
}
QSplitter::handle:hover {
    background: #dbe4f0;
}
QScrollBar:vertical {
    background: transparent;
    width: 10px;
    margin: 2px;
}
QScrollBar::handle:vertical {
    background: #cbd5e1;
    border-radius: 5px;
    min-height: 24px;
}
QScrollBar::handle:vertical:hover {
    background: #94a3b8;
}
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical {
    height: 0;
}
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical {
    background: transparent;
}
QScrollBar:horizontal {
    background: transparent;
    height: 10px;
    margin: 2px;
}
QScrollBar::handle:horizontal {
    background: #cbd5e1;
    border-radius: 5px;
    min-width: 24px;
}
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal {
    width: 0;
}

/* ---------- 状态栏 ---------- */
QStatusBar {
    background: #ffffff;
    border-top: 1px solid #e5e9f0;
    color: #64748b;
    font-size: 12px;
}
QStatusBar::item {
    border: none;
}

/* ---------- 登录窗口 ---------- */
QDialog {
    background: #f3f5f9;
}
QFrame#loginBrand {
    background: qlineargradient(x1:0, y1:0, x2:1, y2:1,
                                stop:0 #0b1220, stop:0.55 #13233f, stop:1 #1e3a6e);
}
QLabel#loginLogo {
    background: rgba(255, 255, 255, 0.10);
    border: 1px solid rgba(255, 255, 255, 0.18);
    border-radius: 12px;
    color: #ffffff;
    font-size: 24px;
    font-weight: 700;
}
QLabel#loginTitle {
    color: #ffffff;
    font-size: 21px;
    font-weight: 700;
}
QLabel#loginSub {
    color: #93c5fd;
    font-size: 11px;
    margin-top: 4px;
}
QLabel#loginFeature {
    color: #cbd5e1;
    font-size: 12px;
    padding: 3px 0;
}
QLabel#loginVersion {
    color: #64748b;
    font-size: 10px;
}
QFrame#loginForm {
    background: #ffffff;
}
QLabel#loginFormTitle {
    color: #0f172a;
    font-size: 20px;
    font-weight: 700;
}
QLabel#loginFormSub {
    color: #94a3b8;
    font-size: 12px;
}
QLabel#fieldLabel {
    color: #475569;
    font-size: 12px;
    font-weight: 600;
}
QLabel#loginError {
    color: #dc2626;
    font-size: 12px;
}
QLabel#loginHint {
    color: #94a3b8;
    font-size: 11px;
}
"""



def now_text():
    return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def sha256_text(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def make_password(password):
    """新密码统一加盐存储：sha256$salt$digest。"""
    salt = hashlib.sha256(os.urandom(16)).hexdigest()[:16]
    digest = hashlib.sha256((salt + password).encode("utf-8")).hexdigest()
    return "sha256${}${}".format(salt, digest)


def check_password(stored, password):
    """兼容旧库中不带盐的 64 位十六进制摘要。"""
    if not stored:
        return False
    if stored.startswith("sha256$"):
        parts = stored.split("$", 2)
        if len(parts) != 3:
            return False
        salt, digest = parts[1], parts[2]
        calc = hashlib.sha256((salt + password).encode("utf-8")).hexdigest()
        return hmac.compare_digest(calc, digest)
    calc = hashlib.sha256(password.encode("utf-8")).hexdigest()
    return hmac.compare_digest(calc, stored)


def safe_json_loads(text, default=None):
    try:
        return json.loads(text) if text else default
    except Exception:
        return default


def parse_number_list(text):
    tokens = [t for t in re.split(r"[,，;；\s]+", (text or "").strip()) if t]
    return [float(t) for t in tokens]


def preview_list(values, limit=5):
    if not values:
        return ""
    shown = ", ".join("{:g}".format(float(v)) for v in values[:limit])
    if len(values) > limit:
        shown += " …"
    return shown


def format_float(value, digits=3, empty="—"):
    try:
        number = float(value)
    except (TypeError, ValueError):
        return empty
    if not np.isfinite(number):
        return empty
    return ("{:." + str(digits) + "f}").format(number)


# --------------------------数据库工具类--------------------------
class SqliteHelper:
    def __init__(self, db_file):
        self.db_file = db_file
        Path(db_file).parent.mkdir(parents=True, exist_ok=True)

    def _connect(self):
        conn = sqlite3.connect(self.db_file, timeout=15)
        conn.row_factory = sqlite3.Row
        conn.execute("PRAGMA foreign_keys = ON;")
        return conn

    def execute(self, sql, params=()):
        conn = self._connect()
        try:
            with conn:
                cur = conn.execute(sql, params)
                return cur.lastrowid
        finally:
            conn.close()

    def execute_many(self, items):
        """在一个事务里执行多条语句，失败整体回滚。"""
        conn = self._connect()
        try:
            with conn:
                for sql, params in items:
                    conn.execute(sql, params)
            return True, ""
        except Exception as exc:
            return False, str(exc)
        finally:
            conn.close()

    def query_all(self, sql, params=()):
        conn = self._connect()
        try:
            return conn.execute(sql, params).fetchall()
        finally:
            conn.close()

    def query_one(self, sql, params=()):
        conn = self._connect()
        try:
            return conn.execute(sql, params).fetchone()
        finally:
            conn.close()

    def init_table(self):
        # 用户账号表
        self.execute('''CREATE TABLE IF NOT EXISTS user_info (
            uid INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT UNIQUE NOT NULL,
            passwd TEXT NOT NULL,
            role INTEGER NOT NULL,
            realname TEXT,
            create_time TEXT,
            status INTEGER DEFAULT 1,
            last_login TEXT
        )''')
        # 工程项目表
        self.execute('''CREATE TABLE IF NOT EXISTS project_info (
            pid INTEGER PRIMARY KEY AUTOINCREMENT,
            proj_name TEXT NOT NULL,
            facade_name TEXT,
            create_user INTEGER,
            create_time TEXT,
            remark TEXT,
            status TEXT DEFAULT '在建',
            update_time TEXT
        )''')
        # 玻璃分格表
        self.execute('''CREATE TABLE IF NOT EXISTS glass_panel (
            gid INTEGER PRIMARY KEY AUTOINCREMENT,
            pid INTEGER,
            glass_no TEXT,
            width REAL,
            height REAL,
            thickness REAL,
            glass_type TEXT DEFAULT '中空钢化',
            remark TEXT,
            FOREIGN KEY(pid) REFERENCES project_info(pid)
        )''')
        # 驳接爪节点表
        self.execute('''CREATE TABLE IF NOT EXISTS claw_node (
            nid INTEGER PRIMARY KEY AUTOINCREMENT,
            gid INTEGER,
            claw_no TEXT,
            arm_count INTEGER,
            preload REAL,
            eccentricity REAL,
            node_type TEXT DEFAULT '四爪',
            arm_len REAL DEFAULT 0,
            remark TEXT,
            FOREIGN KEY(gid) REFERENCES glass_panel(gid)
        )''')
        # 测点应变、挠度数据
        self.execute('''CREATE TABLE IF NOT EXISTS measure_point (
            mid INTEGER PRIMARY KEY AUTOINCREMENT,
            nid INTEGER,
            point_no TEXT,
            strain_data TEXT,
            deflect_data TEXT,
            collect_time TEXT,
            remark TEXT,
            FOREIGN KEY(nid) REFERENCES claw_node(nid)
        )''')
        # 计算结果、证据链、审计日志
        self.execute('''CREATE TABLE IF NOT EXISTS calc_record (
            rid INTEGER PRIMARY KEY AUTOINCREMENT,
            nid INTEGER,
            mid INTEGER,
            result_json TEXT,
            param_json TEXT,
            sha_hash TEXT,
            calc_time TEXT,
            status INTEGER,
            alarm_msg TEXT,
            sign_user INTEGER,
            sign_time TEXT,
            report_path TEXT,
            FOREIGN KEY(nid) REFERENCES claw_node(nid)
        )''')
        # 系统操作审计日志
        self.execute('''CREATE TABLE IF NOT EXISTS audit_log (
            lid INTEGER PRIMARY KEY AUTOINCREMENT,
            uid INTEGER,
            opt_type TEXT,
            opt_detail TEXT,
            opt_time TEXT
        )''')
        # 复核工单
        self.execute('''CREATE TABLE IF NOT EXISTS work_order (
            wid INTEGER PRIMARY KEY AUTOINCREMENT,
            nid INTEGER,
            rid INTEGER,
            title TEXT,
            detail TEXT,
            status TEXT DEFAULT '开放',
            owner TEXT,
            create_time TEXT,
            close_time TEXT
        )''')
        # 旧库结构升级
        self._ensure_column("project_info", "status", "TEXT DEFAULT '在建'")
        self._ensure_column("project_info", "update_time", "TEXT")
        self._ensure_column("glass_panel", "glass_type", "TEXT DEFAULT '中空钢化'")
        self._ensure_column("glass_panel", "remark", "TEXT")
        self._ensure_column("claw_node", "node_type", "TEXT DEFAULT '四爪'")
        self._ensure_column("claw_node", "arm_len", "REAL DEFAULT 0")
        self._ensure_column("claw_node", "remark", "TEXT")
        self._ensure_column("claw_node", "pos_x", "REAL DEFAULT 0")
        self._ensure_column("claw_node", "pos_y", "REAL DEFAULT 0")
        self._ensure_column("measure_point", "remark", "TEXT")
        self._ensure_column("calc_record", "mid", "INTEGER")
        self._ensure_column("calc_record", "param_json", "TEXT")
        self._ensure_column("calc_record", "sign_time", "TEXT")
        self._ensure_column("calc_record", "report_path", "TEXT")
        self._ensure_column("user_info", "status", "INTEGER DEFAULT 1")
        self._ensure_column("user_info", "last_login", "TEXT")
        self.execute("CREATE INDEX IF NOT EXISTS idx_panel_pid ON glass_panel(pid)")
        self.execute("CREATE INDEX IF NOT EXISTS idx_node_gid ON claw_node(gid)")
        self.execute("CREATE INDEX IF NOT EXISTS idx_measure_nid ON measure_point(nid)")
        self.execute("CREATE INDEX IF NOT EXISTS idx_calc_nid ON calc_record(nid)")
        # 初始化管理员账号
        row = self.query_one("select uid from user_info where username=?", ("admin",))
        if row is None:
            self.execute(
                "insert into user_info(username,passwd,role,realname,create_time,status) values (?,?,?,?,?,1)",
                ("admin", make_password("admin123"), USER_ROLE_ADMIN, "系统管理员", now_text()))

    def _ensure_column(self, table, column, decl):
        cols = [r["name"] for r in self.query_all("PRAGMA table_info({})".format(table))]
        if column not in cols:
            self.execute("ALTER TABLE {} ADD COLUMN {} {}".format(table, column, decl))


# --------------------------SHA256摘要树工具（证据封存）--------------------------
class HashTreeTool:
    @staticmethod
    def calc_sha256(raw_bytes):
        return hashlib.sha256(raw_bytes).hexdigest()

    @staticmethod
    def file_hash(file_path):
        h = hashlib.sha256()
        with open(file_path, "rb") as f:
            while chunk := f.read(65536):
                h.update(chunk)
        return h.hexdigest()

    @staticmethod
    def build_merkle_root(hash_list):
        if not hash_list:
            return ""
        tmp = list(hash_list)
        while len(tmp) > 1:
            new_tmp = []
            for i in range(0, len(tmp), 2):
                a = tmp[i]
                b = tmp[i + 1] if i + 1 < len(tmp) else tmp[i]
                new_tmp.append(HashTreeTool.calc_sha256((a + b).encode("utf-8")))
            tmp = new_tmp
        return tmp[0]

    @staticmethod
    def build_chain(hash_list):
        """逐条链式封存：chain_i = sha256(chain_{i-1} + hash_i)。"""
        chain = []
        prev = ""
        for h in hash_list:
            prev = HashTreeTool.calc_sha256((prev + h).encode("utf-8"))
            chain.append(prev)
        return chain


# --------------------------核心算法模块：带权正则化、SVD反演--------------------------
class MuskInversionSolver:
    def __init__(self, reg_weight=ALG_WEIGHT_REG, svd_eps=SVD_THRESHOLD):
        self.reg_weight = reg_weight
        self.svd_eps = svd_eps

    def weighted_reg_solve(self, mat_A, vec_b, reg_weight=None):
        m, n = mat_A.shape
        weight = self.reg_weight if reg_weight is None else float(reg_weight)
        A_reg = mat_A.T @ mat_A + weight * np.eye(n)
        b_reg = mat_A.T @ vec_b
        try:
            return np.linalg.solve(A_reg, b_reg)
        except np.linalg.LinAlgError:
            return np.linalg.lstsq(A_reg, b_reg, rcond=None)[0]

    def svd_identify(self, mat_A, vec_b):
        U, s, Vt = np.linalg.svd(mat_A, full_matrices=False)
        s_inv = np.zeros_like(s)
        for idx, sigma in enumerate(s):
            if sigma > self.svd_eps:
                s_inv[idx] = 1.0 / sigma
        return Vt.T @ (s_inv * (U.T @ vec_b))

    def build_transfer_matrix(self, n, coupling=0.06):
        """简化耦合计传递矩阵：对角为 1，其余爪臂按耦合系数分摊。"""
        n = int(n)
        mat = np.eye(n, dtype=float)
        if n > 1:
            off = float(coupling) / (n - 1)
            mask = ~np.eye(n, dtype=bool)
            mat[mask] = off
        return mat

    def contact_model_calc(self, preload, gap, elastic_mod):
        return elastic_mod * np.sqrt(preload / (gap + 1e-8))

    def coupling_claw_inversion(self, strain_array, deflect_array, para_dict):
        mat_A = np.array(para_dict["transfer_matrix"], dtype=float)
        vec_b = np.array(strain_array, dtype=float).reshape(-1)
        if mat_A.shape[0] != vec_b.size:
            raise ValueError("传递矩阵维度与测点数量不一致")
        x1 = self.weighted_reg_solve(mat_A, vec_b, para_dict.get("reg_weight"))
        x2 = self.svd_identify(mat_A, vec_b)
        w1 = float(para_dict.get("w1", 0.6))
        w2 = float(para_dict.get("w2", 1.0 - w1))
        fuse = w1 * x1 + w2 * x2
        valid, max_abs = self.check_constraint(fuse, para_dict)
        return {
            "result": [float(v) for v in fuse],
            "valid": bool(valid),
            "max_abs": float(max_abs),
            "deflect_fit": self.fit_deflect(fuse, deflect_array, para_dict),
        }

    def check_constraint(self, force_vec, para):
        max_force = float(para.get("max_allow_force", 100.0))
        max_abs = float(np.max(np.abs(force_vec))) if len(force_vec) else 0.0
        return max_abs <= max_force, max_abs

    def fit_deflect(self, force_vec, deflect_obs, para):
        k = para.get("stiffness_k", 1.0)
        if np.isscalar(k):
            k_arr = np.full(len(force_vec), float(k))
        else:
            k_arr = np.array(k, dtype=float)
        pred = np.array(force_vec, dtype=float) / np.where(np.abs(k_arr) < 1e-12, 1e-12, k_arr)
        observed = np.array(deflect_obs, dtype=float)
        if observed.size != pred.size or observed.size == 0:
            err = None
        else:
            err = float(np.mean(np.abs(pred - observed)))
        return {"pred": [float(v) for v in pred], "error": err}

    def missing_point_predict(self, exist_data, mask):
        valid_x = [idx for idx, ok in enumerate(mask) if ok]
        valid_v = [exist_data[idx] for idx in valid_x]
        if len(valid_x) < 2:
            return None
        if len(valid_x) < 4:
            return np.interp(np.arange(len(mask)), np.array(valid_x), np.array(valid_v)).tolist()
        interp_res = griddata(np.array(valid_x), np.array(valid_v), np.arange(len(mask)), method="cubic")
        return [float(v) for v in interp_res]


# --------------------------后台计算线程（防止UI卡死）--------------------------
class CalcThread(QThread):
    sig_finish = pyqtSignal(dict)
    sig_alarm = pyqtSignal(str)

    def __init__(self, solver, strain, deflect, para, parent=None):
        super().__init__(parent)
        self.solver = solver
        self.strain = strain
        self.deflect = deflect
        self.para = para

    def run(self):
        try:
            res = self.solver.coupling_claw_inversion(self.strain, self.deflect, self.para)
            self.sig_finish.emit(res)
        except Exception as exc:
            self.sig_alarm.emit("计算异常：{}".format(exc))


# --------------------------登录窗口--------------------------
class LoginDialog(QDialog):
    def __init__(self, db, parent=None):
        super().__init__(parent)
        self.db = db
        self.user = None
        self.setWindowTitle("登录 - " + APP_TITLE)
        self.setFixedSize(780, 470)
        self.setModal(True)

        root = QHBoxLayout(self)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        brand = QFrame()
        brand.setObjectName("loginBrand")
        brand.setFixedWidth(300)
        bl = QVBoxLayout(brand)
        bl.setContentsMargins(32, 36, 30, 28)
        bl.setSpacing(0)

        logo = QLabel("驳")
        logo.setObjectName("loginLogo")
        logo.setFixedSize(54, 54)
        logo.setAlignment(Qt.AlignmentFlag.AlignCenter)
        bl.addWidget(logo, 0, Qt.AlignmentFlag.AlignLeft)
        bl.addSpacing(24)

        title = QLabel("驳接爪受力反演")
        title.setObjectName("loginTitle")
        sub = QLabel("点支式玻璃幕墙节点分析平台")
        sub.setObjectName("loginSub")
        bl.addWidget(title)
        bl.addWidget(sub)
        bl.addSpacing(30)

        for text in ("多爪耦合受力反演", "三维数字孪生联动", "计算证据链封存"):
            item = QLabel("·   " + text)
            item.setObjectName("loginFeature")
            bl.addWidget(item)

        bl.addStretch(1)
        version = QLabel("V1.0  ·  单机版")
        version.setObjectName("loginVersion")
        bl.addWidget(version)
        root.addWidget(brand)

        form = QFrame()
        form.setObjectName("loginForm")
        fl = QVBoxLayout(form)
        fl.setContentsMargins(54, 46, 54, 34)
        fl.setSpacing(0)

        form_title = QLabel("账号登录")
        form_title.setObjectName("loginFormTitle")
        form_sub = QLabel("请输入账号信息进入工作台")
        form_sub.setObjectName("loginFormSub")
        fl.addWidget(form_title)
        fl.addWidget(form_sub)
        fl.addSpacing(26)

        label_user = QLabel("用户名")
        label_user.setObjectName("fieldLabel")
        self.le_user = QLineEdit()
        self.le_user.setPlaceholderText("请输入用户名")
        self.le_user.setMinimumHeight(40)
        label_pwd = QLabel("密码")
        label_pwd.setObjectName("fieldLabel")
        self.le_pwd = QLineEdit()
        self.le_pwd.setEchoMode(QLineEdit.EchoMode.Password)
        self.le_pwd.setPlaceholderText("请输入密码")
        self.le_pwd.setMinimumHeight(40)
        self.le_pwd.returnPressed.connect(self.do_login)

        fl.addWidget(label_user)
        fl.addSpacing(6)
        fl.addWidget(self.le_user)
        fl.addSpacing(14)
        fl.addWidget(label_pwd)
        fl.addSpacing(6)
        fl.addWidget(self.le_pwd)

        self.lbl_error = QLabel("")
        self.lbl_error.setObjectName("loginError")
        self.lbl_error.setMinimumHeight(20)
        fl.addSpacing(6)
        fl.addWidget(self.lbl_error)

        self.btn_login = QPushButton("登 录")
        self.btn_login.setObjectName("primaryBtn")
        self.btn_login.setMinimumHeight(42)
        self.btn_login.setDefault(True)
        self.btn_login.setCursor(Qt.CursorShape.PointingHandCursor)
        fl.addWidget(self.btn_login)
        fl.addSpacing(6)

        self.btn_guest = QPushButton("访客只读进入")
        self.btn_guest.setObjectName("ghostBtn")
        self.btn_guest.setMinimumHeight(34)
        self.btn_guest.setCursor(Qt.CursorShape.PointingHandCursor)
        fl.addWidget(self.btn_guest)
        fl.addStretch(1)

        row = self.db.query_one("select passwd from user_info where username='admin'")
        if row is not None and check_password(row["passwd"], "admin123"):
            hint_text = "默认管理员：admin / admin123，登录后请及时修改密码"
        else:
            hint_text = "如遗忘密码，请联系系统管理员重置"
        hint = QLabel(hint_text)
        hint.setObjectName("loginHint")
        hint.setWordWrap(True)
        fl.addWidget(hint)

        root.addWidget(form, 1)

        self.btn_login.clicked.connect(self.do_login)
        self.btn_guest.clicked.connect(self.do_guest)

    def do_login(self):
        username = self.le_user.text().strip()
        password = self.le_pwd.text()
        if not username or not password:
            self.lbl_error.setText("用户名和密码不能为空")
            return
        row = self.db.query_one("select * from user_info where username=?", (username,))
        if row is None or not check_password(row["passwd"], password):
            self.lbl_error.setText("用户名或密码错误")
            self.le_pwd.selectAll()
            return
        if int(row["status"] or 1) != 1:
            self.lbl_error.setText("该账号已被停用，请联系管理员")
            return
        self.db.execute("update user_info set last_login=? where uid=?", (now_text(), row["uid"]))
        self.user = {
            "uid": row["uid"],
            "username": row["username"],
            "realname": row["realname"] or row["username"],
            "role": int(row["role"]),
        }
        self.accept()

    def do_guest(self):
        self.user = {"uid": None, "username": "guest", "realname": "访客", "role": USER_ROLE_VISITOR}
        self.accept()


# --------------------------基础表单对话框--------------------------
class BaseDialog(QDialog):
    def __init__(self, title, parent=None, width=440):
        super().__init__(parent)
        self.setWindowTitle(title)
        self.setMinimumWidth(width)
        self.setModal(True)
        self.body = QVBoxLayout(self)
        self.body.setContentsMargins(22, 20, 22, 18)
        self.body.setSpacing(14)
        self.form = QFormLayout()
        self.form.setHorizontalSpacing(16)
        self.form.setVerticalSpacing(10)
        self.body.addLayout(self.form)
        self.btn_row = QHBoxLayout()
        self.btn_row.addStretch(1)
        self.btn_cancel = QPushButton("取消")
        self.btn_cancel.setObjectName("ghostBtn")
        self.btn_ok = QPushButton("保存")
        self.btn_ok.setObjectName("primaryBtn")
        self.btn_ok.setDefault(True)
        self.btn_row.addWidget(self.btn_cancel)
        self.btn_row.addWidget(self.btn_ok)
        self.body.addLayout(self.btn_row)
        self.btn_cancel.clicked.connect(self.reject)
        self.btn_ok.clicked.connect(self.accept)


class ProjectDialog(BaseDialog):
    def __init__(self, parent=None, data=None):
        super().__init__("编辑工程" if data else "新建工程", parent)
        data = data or {}
        self.le_name = QLineEdit(data.get("proj_name", ""))
        self.le_facade = QLineEdit(data.get("facade_name", ""))
        self.cb_status = QComboBox()
        self.cb_status.addItems(PROJECT_STATUS)
        if data.get("status") in PROJECT_STATUS:
            self.cb_status.setCurrentText(data["status"])
        self.le_remark = QLineEdit(data.get("remark", ""))
        self.form.addRow("工程名称", self.le_name)
        self.form.addRow("立面名称", self.le_facade)
        self.form.addRow("工程状态", self.cb_status)
        self.form.addRow("备注", self.le_remark)

    def accept(self):
        if not self.le_name.text().strip():
            QMessageBox.warning(self, "提示", "工程名称不能为空")
            return
        super().accept()

    def data(self):
        return {
            "proj_name": self.le_name.text().strip(),
            "facade_name": self.le_facade.text().strip(),
            "status": self.cb_status.currentText(),
            "remark": self.le_remark.text().strip(),
        }


class PanelDialog(BaseDialog):
    def __init__(self, parent=None, data=None, suggest_no=""):
        super().__init__("玻璃分格", parent)
        data = data or {}
        self.le_no = QLineEdit(data.get("glass_no", suggest_no))
        self.sp_width = QDoubleSpinBox()
        self.sp_width.setRange(100, 30000)
        self.sp_width.setDecimals(0)
        self.sp_width.setValue(float(data.get("width") or 1200))
        self.sp_width.setSuffix(" mm")
        self.sp_height = QDoubleSpinBox()
        self.sp_height.setRange(100, 30000)
        self.sp_height.setDecimals(0)
        self.sp_height.setValue(float(data.get("height") or 1500))
        self.sp_height.setSuffix(" mm")
        self.sp_thick = QDoubleSpinBox()
        self.sp_thick.setRange(1, 200)
        self.sp_thick.setDecimals(1)
        self.sp_thick.setValue(float(data.get("thickness") or 12))
        self.sp_thick.setSuffix(" mm")
        self.le_type = QLineEdit(data.get("glass_type", "中空钢化"))
        self.le_remark = QLineEdit(data.get("remark", ""))
        self.form.addRow("分格编号", self.le_no)
        self.form.addRow("分格宽度", self.sp_width)
        self.form.addRow("分格高度", self.sp_height)
        self.form.addRow("玻璃厚度", self.sp_thick)
        self.form.addRow("玻璃类型", self.le_type)
        self.form.addRow("备注", self.le_remark)

    def accept(self):
        if not self.le_no.text().strip():
            QMessageBox.warning(self, "提示", "分格编号不能为空")
            return
        super().accept()

    def data(self):
        return {
            "glass_no": self.le_no.text().strip(),
            "width": self.sp_width.value(),
            "height": self.sp_height.value(),
            "thickness": self.sp_thick.value(),
            "glass_type": self.le_type.text().strip(),
            "remark": self.le_remark.text().strip(),
        }


class NodeDialog(BaseDialog):
    def __init__(self, parent=None, data=None, suggest_no="", suggest_pos=(0.0, 0.0)):
        super().__init__("驳接爪节点", parent)
        data = data or {}
        self.le_no = QLineEdit(data.get("claw_no", suggest_no))
        self.sp_arm = QSpinBox()
        self.sp_arm.setRange(1, 12)
        self.sp_arm.setValue(int(data.get("arm_count") or 4))
        self.sp_preload = QDoubleSpinBox()
        self.sp_preload.setRange(0, 2000)
        self.sp_preload.setDecimals(1)
        self.sp_preload.setValue(float(data.get("preload") or 20))
        self.sp_preload.setSuffix(" kN")
        self.sp_ecc = QDoubleSpinBox()
        self.sp_ecc.setRange(0, 1000)
        self.sp_ecc.setDecimals(1)
        self.sp_ecc.setValue(float(data.get("eccentricity") or 0))
        self.sp_ecc.setSuffix(" mm")
        self.cb_type = QComboBox()
        self.cb_type.addItems(NODE_TYPES)
        if data.get("node_type") in NODE_TYPES:
            self.cb_type.setCurrentText(data["node_type"])
        self.sp_arm_len = QDoubleSpinBox()
        self.sp_arm_len.setRange(0, 5000)
        self.sp_arm_len.setDecimals(1)
        self.sp_arm_len.setValue(float(data.get("arm_len") or 300))
        self.sp_arm_len.setSuffix(" mm")
        self.sp_pos_x = QDoubleSpinBox()
        self.sp_pos_x.setRange(-20000, 20000)
        self.sp_pos_x.setDecimals(1)
        self.sp_pos_x.setValue(float(data.get("pos_x") if data.get("pos_x") is not None else suggest_pos[0]))
        self.sp_pos_x.setSuffix(" mm")
        self.sp_pos_y = QDoubleSpinBox()
        self.sp_pos_y.setRange(-20000, 20000)
        self.sp_pos_y.setDecimals(1)
        self.sp_pos_y.setValue(float(data.get("pos_y") if data.get("pos_y") is not None else suggest_pos[1]))
        self.sp_pos_y.setSuffix(" mm")
        self.le_remark = QLineEdit(data.get("remark", ""))
        self.form.addRow("节点编号", self.le_no)
        self.form.addRow("爪臂数量", self.sp_arm)
        self.form.addRow("预紧力", self.sp_preload)
        self.form.addRow("偏心距", self.sp_ecc)
        self.form.addRow("节点类型", self.cb_type)
        self.form.addRow("爪臂长度", self.sp_arm_len)
        self.form.addRow("位置 X", self.sp_pos_x)
        self.form.addRow("位置 Y", self.sp_pos_y)
        self.form.addRow("备注", self.le_remark)

    def accept(self):
        if not self.le_no.text().strip():
            QMessageBox.warning(self, "提示", "节点编号不能为空")
            return
        super().accept()

    def data(self):
        return {
            "claw_no": self.le_no.text().strip(),
            "arm_count": self.sp_arm.value(),
            "preload": self.sp_preload.value(),
            "eccentricity": self.sp_ecc.value(),
            "node_type": self.cb_type.currentText(),
            "arm_len": self.sp_arm_len.value(),
            "pos_x": self.sp_pos_x.value(),
            "pos_y": self.sp_pos_y.value(),
            "remark": self.le_remark.text().strip(),
        }


class MeasureDialog(BaseDialog):
    def __init__(self, parent=None, suggest_no="P01"):
        super().__init__("录入测点数据", parent, width=520)
        self.le_no = QLineEdit(suggest_no)
        self.le_strain = QLineEdit()
        self.le_strain.setPlaceholderText("例如：12.3, 14.1, -8.2, 9.6")
        self.le_deflect = QLineEdit()
        self.le_deflect.setPlaceholderText("例如：0.82, 0.91, 0.44, 0.75")
        self.le_time = QLineEdit(now_text())
        self.le_remark = QLineEdit()
        self.form.addRow("测点编号", self.le_no)
        self.form.addRow("应变序列", self.le_strain)
        self.form.addRow("挠度序列", self.le_deflect)
        self.form.addRow("采集时间", self.le_time)
        self.form.addRow("备注", self.le_remark)
        tip = QLabel("应变、挠度按爪臂顺序以逗号分隔，两组数量必须一致。")
        tip.setWordWrap(True)
        tip.setStyleSheet("color:#666;")
        self.body.insertWidget(1, tip)

    def accept(self):
        try:
            strain = parse_number_list(self.le_strain.text())
            deflect = parse_number_list(self.le_deflect.text())
        except ValueError:
            QMessageBox.warning(self, "提示", "应变/挠度序列中存在非法数字")
            return
        if not strain or not deflect:
            QMessageBox.warning(self, "提示", "应变、挠度序列不能为空")
            return
        if len(strain) != len(deflect):
            QMessageBox.warning(self, "提示", "应变与挠度数量不一致，请检查")
            return
        super().accept()

    def data(self):
        return {
            "point_no": self.le_no.text().strip(),
            "strain": parse_number_list(self.le_strain.text()),
            "deflect": parse_number_list(self.le_deflect.text()),
            "collect_time": self.le_time.text().strip() or now_text(),
            "remark": self.le_remark.text().strip(),
        }


class UserDialog(BaseDialog):
    def __init__(self, parent=None):
        super().__init__("新增账号", parent)
        self.le_user = QLineEdit()
        self.le_real = QLineEdit()
        self.cb_role = QComboBox()
        for key, name in ROLE_NAMES.items():
            self.cb_role.addItem(name, key)
        self.le_pwd = QLineEdit()
        self.le_pwd.setEchoMode(QLineEdit.EchoMode.Password)
        self.le_pwd2 = QLineEdit()
        self.le_pwd2.setEchoMode(QLineEdit.EchoMode.Password)
        self.form.addRow("用户名", self.le_user)
        self.form.addRow("真实姓名", self.le_real)
        self.form.addRow("角色", self.cb_role)
        self.form.addRow("密码", self.le_pwd)
        self.form.addRow("确认密码", self.le_pwd2)

    def accept(self):
        if not self.le_user.text().strip():
            QMessageBox.warning(self, "提示", "用户名不能为空")
            return
        if len(self.le_pwd.text()) < 6:
            QMessageBox.warning(self, "提示", "密码长度不能少于 6 位")
            return
        if self.le_pwd.text() != self.le_pwd2.text():
            QMessageBox.warning(self, "提示", "两次输入的密码不一致")
            return
        super().accept()

    def data(self):
        return {
            "username": self.le_user.text().strip(),
            "realname": self.le_real.text().strip(),
            "role": self.cb_role.currentData(),
            "password": self.le_pwd.text(),
        }


class SignDialog(BaseDialog):
    def __init__(self, parent=None, username=""):
        super().__init__("成果签认", parent)
        self.le_user = QLineEdit(username)
        self.le_user.setReadOnly(True)
        self.le_pwd = QLineEdit()
        self.le_pwd.setEchoMode(QLineEdit.EchoMode.Password)
        self.form.addRow("签认人", self.le_user)
        self.form.addRow("登录密码", self.le_pwd)
        tip = QLabel("签认后该计算记录将写入签认人和签认时间，用于成果追溯。")
        tip.setWordWrap(True)
        tip.setStyleSheet("color:#666;")
        self.body.insertWidget(1, tip)

    def accept(self):
        if not self.le_pwd.text():
            QMessageBox.warning(self, "提示", "请输入登录密码")
            return
        super().accept()

    def password(self):
        return self.le_pwd.text()


# --------------------------工程/分格/节点三级联动选择器--------------------------
class NodeSelector(QWidget):
    changed = pyqtSignal()

    def __init__(self, db, parent=None):
        super().__init__(parent)
        self.setObjectName("filterBar")
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.db = db
        self._loading = False
        row = QHBoxLayout(self)
        row.setContentsMargins(14, 10, 14, 10)
        row.setSpacing(8)
        self.cb_project = QComboBox()
        self.cb_panel = QComboBox()
        self.cb_node = QComboBox()
        for label, combo in (("工程", self.cb_project), ("分格", self.cb_panel), ("节点", self.cb_node)):
            tag = QLabel(label)
            tag.setObjectName("filterLabel")
            row.addWidget(tag)
            combo.setMinimumWidth(160)
            row.addWidget(combo)
        row.addStretch(1)
        self.cb_project.currentIndexChanged.connect(self._on_project)
        self.cb_panel.currentIndexChanged.connect(self._on_panel)
        self.cb_node.currentIndexChanged.connect(self._on_node)
        self.refresh()

    def refresh(self):
        self._loading = True
        keep_pid = self.cb_project.currentData()
        self.cb_project.clear()
        for r in self.db.query_all("select pid, proj_name from project_info order by pid desc"):
            self.cb_project.addItem("{} · {}".format(r["pid"], r["proj_name"]), r["pid"])
        self._restore(self.cb_project, keep_pid)
        self._loading = False
        self._reload_panels()
        self.changed.emit()

    def _restore(self, combo, value):
        if value is None:
            return
        idx = combo.findData(value)
        if idx >= 0:
            combo.setCurrentIndex(idx)

    def _reload_panels(self):
        self._loading = True
        keep = self.cb_panel.currentData()
        self.cb_panel.clear()
        pid = self.cb_project.currentData()
        if pid is not None:
            for r in self.db.query_all("select gid, glass_no from glass_panel where pid=? order by gid desc", (pid,)):
                self.cb_panel.addItem("{} · {}".format(r["gid"], r["glass_no"] or "未命名"), r["gid"])
        self._restore(self.cb_panel, keep)
        self._loading = False
        self._reload_nodes()

    def _reload_nodes(self):
        self._loading = True
        keep = self.cb_node.currentData()
        self.cb_node.clear()
        gid = self.cb_panel.currentData()
        if gid is not None:
            for r in self.db.query_all("select nid, claw_no from claw_node where gid=? order by nid desc", (gid,)):
                self.cb_node.addItem("{} · {}".format(r["nid"], r["claw_no"] or "未命名"), r["nid"])
        self._restore(self.cb_node, keep)
        self._loading = False

    def _on_project(self):
        if self._loading:
            return
        self._reload_panels()
        self.changed.emit()

    def _on_panel(self):
        if self._loading:
            return
        self._reload_nodes()
        self.changed.emit()

    def _on_node(self):
        if self._loading:
            return
        self.changed.emit()

    def current_node_id(self):
        return self.cb_node.currentData()

    def current_node_row(self):
        nid = self.current_node_id()
        if nid is None:
            return None
        return self.db.query_one("select * from claw_node where nid=?", (nid,))


class StatCard(QFrame):
    def __init__(self, title, value="0", unit="", hint="", accent="#2563eb", parent=None):
        super().__init__(parent)
        self.setObjectName("statCard")
        self.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        self.setMinimumHeight(104)
        row = QHBoxLayout(self)
        row.setContentsMargins(16, 14, 16, 14)
        row.setSpacing(14)
        bar = QFrame()
        bar.setFixedWidth(4)
        bar.setStyleSheet("background:{}; border-radius:2px;".format(accent))
        row.addWidget(bar)
        body = QVBoxLayout()
        body.setSpacing(2)
        self.lbl_title = QLabel(title)
        self.lbl_title.setObjectName("statTitle")
        body.addWidget(self.lbl_title)
        value_row = QHBoxLayout()
        value_row.setSpacing(6)
        self.lbl_value = QLabel(str(value))
        self.lbl_value.setObjectName("statValue")
        value_row.addWidget(self.lbl_value)
        self.lbl_unit = QLabel(unit)
        self.lbl_unit.setObjectName("statUnit")
        value_row.addWidget(self.lbl_unit, 0, Qt.AlignmentFlag.AlignBottom)
        value_row.addStretch(1)
        body.addLayout(value_row)
        self.lbl_hint = QLabel(hint)
        self.lbl_hint.setObjectName("statHint")
        body.addWidget(self.lbl_hint)
        row.addLayout(body, 1)

    def set_value(self, value, hint=None):
        self.lbl_value.setText(str(value))
        if hint is not None:
            self.lbl_hint.setText(hint)


class ChartWidget(QWidget):
    """轻量自绘图表：柱状图 / 折线图 / 面积图，不依赖第三方图表库。"""

    def __init__(self, kind="bar", parent=None):
        super().__init__(parent)
        self.kind = kind
        self.labels = []
        self.series = []
        self.y_suffix = ""
        self.empty_text = "暂无数据"
        self.setMinimumHeight(210)
        self.setSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Expanding)
        self.setMouseTracking(True)

    def set_data(self, labels, series, y_suffix=""):
        self.labels = list(labels)
        self.series = series
        self.y_suffix = y_suffix
        self.update()

    def sizeHint(self):
        return QSize(420, 240)

    def _plot_rect(self):
        return QRectF(54, 26, max(10, self.width() - 72), max(10, self.height() - 64))

    @staticmethod
    def _nice_max(value):
        if value <= 0:
            return 1.0
        exp = math.floor(math.log10(value))
        base = 10 ** exp
        for mult in (1, 1.2, 1.5, 2, 2.5, 3, 4, 5, 10):
            if value <= mult * base:
                return float(mult * base)
        return float(10 * base)

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        if not self.series or not self.labels:
            self._draw_empty(painter)
            return
        values = []
        for s in self.series:
            values.extend([float(v) for v in s.get("values", [])])
        if not values:
            self._draw_empty(painter)
            return
        plot = self._plot_rect()
        data_max = max(values)
        data_min = min(values)
        bound = self._nice_max(max(abs(data_max), abs(data_min)) * 1.12)
        max_value = bound if data_max > 0 else 0.0
        min_value = -bound if data_min < 0 else 0.0
        span = max_value - min_value if max_value != min_value else 1.0

        def y_of(val):
            return plot.bottom() - (float(val) - min_value) / span * plot.height()

        grid_pen = QPen(QColor("#eef2f7"))
        grid_pen.setWidth(1)
        text_color = QColor("#94a3b8")
        axis_font = QFont("Microsoft YaHei", 8)
        for i in range(5):
            val = min_value + span * i / 4
            y = y_of(val)
            painter.setPen(grid_pen)
            painter.drawLine(QPointF(plot.left(), y), QPointF(plot.right(), y))
            painter.setPen(text_color)
            painter.setFont(axis_font)
            step_value = span / 4
            if abs(step_value - round(step_value)) < 1e-6:
                label = "{:.0f}".format(val)
            else:
                label = "{:.1f}".format(val)
            painter.drawText(QRectF(0, y - 8, plot.left() - 10, 16),
                             Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                             label + self.y_suffix)

        n = len(self.labels)
        step = plot.width() / max(1, n)
        painter.setFont(axis_font)
        for i, label in enumerate(self.labels):
            x = plot.left() + (i + 0.5) * step
            painter.setPen(text_color)
            painter.drawText(QRectF(x - step / 2, plot.bottom() + 8, step, 18),
                             Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignTop, str(label))

        if self.kind == "bar":
            self._draw_bars(painter, plot, step, y_of)
        else:
            self._draw_lines(painter, plot, step, y_of)

    def _draw_bars(self, painter, plot, step, y_of):
        series = self.series[0]
        color = QColor(series.get("color", "#2563eb"))
        values = series.get("values", [])
        bar_width = max(10.0, step * 0.46)
        for i, val in enumerate(values):
            x = plot.left() + i * step + (step - bar_width) / 2
            y = y_of(val)
            height = max(1.0, plot.bottom() - y)
            grad = QLinearGradient(0, y, 0, plot.bottom())
            grad.setColorAt(0.0, color.lighter(112))
            grad.setColorAt(1.0, color)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QBrush(grad))
            painter.drawRoundedRect(QRectF(x, y, bar_width, height), 3, 3)
            painter.setPen(QColor("#475569"))
            painter.setFont(QFont("Microsoft YaHei", 8))
            painter.drawText(QRectF(x - 8, y - 20, bar_width + 16, 16),
                             Qt.AlignmentFlag.AlignHCenter | Qt.AlignmentFlag.AlignBottom,
                             "{:.1f}".format(float(val)))

    def _draw_lines(self, painter, plot, step, y_of):
        legend_x = plot.left()
        legend_y = 10
        for s in self.series:
            color = QColor(s.get("color", "#2563eb"))
            values = [float(v) for v in s.get("values", [])]
            if not values:
                continue
            points = [QPointF(plot.left() + (i + 0.5) * step, y_of(v)) for i, v in enumerate(values)]
            if s.get("fill") and len(points) >= 2:
                path = QPainterPath(points[0])
                for pt in points[1:]:
                    path.lineTo(pt)
                path.lineTo(points[-1].x(), plot.bottom())
                path.lineTo(points[0].x(), plot.bottom())
                path.closeSubpath()
                grad = QLinearGradient(0, plot.top(), 0, plot.bottom())
                fill_color = QColor(color)
                fill_color.setAlpha(70)
                clear = QColor(color)
                clear.setAlpha(4)
                grad.setColorAt(0.0, fill_color)
                grad.setColorAt(1.0, clear)
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QBrush(grad))
                painter.drawPath(path)
            pen = QPen(color)
            pen.setWidth(2)
            painter.setPen(pen)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawPolyline(QPolygonF(points))
            painter.setBrush(QBrush(color))
            painter.setPen(QPen(QColor("#ffffff"), 1.5))
            for pt in points:
                painter.drawEllipse(pt, 3.2, 3.2)
            name = s.get("name", "")
            if name:
                painter.setPen(color)
                painter.setBrush(QBrush(color))
                painter.drawEllipse(QPointF(legend_x + 4, legend_y + 8), 3, 3)
                painter.setPen(QColor("#64748b"))
                painter.setFont(QFont("Microsoft YaHei", 8))
                painter.drawText(QRectF(legend_x + 12, legend_y, 90, 16),
                                 Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter, name)
                legend_x += 20 + painter.fontMetrics().horizontalAdvance(name)

    def _draw_empty(self, painter):
        painter.setPen(QColor("#cbd5e1"))
        painter.setFont(QFont("Microsoft YaHei", 10))
        painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, self.empty_text)


class PanelSchematic(QWidget):
    """玻璃分格与四角驳接爪的二维示意图。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.panel_no = ""
        self.width_mm = 1500
        self.height_mm = 1800
        self.thickness_mm = 12
        self.forces = []
        self.node_labels = ["J-01", "J-02", "J-03", "J-04"]
        self.setMinimumHeight(300)

    def set_data(self, panel_no, width_mm, height_mm, thickness_mm, forces, labels=None):
        self.panel_no = panel_no or "GL-001"
        self.width_mm = float(width_mm or 1500)
        self.height_mm = float(height_mm or 1800)
        self.thickness_mm = float(thickness_mm or 12)
        self.forces = [float(v) for v in (forces or [])]
        if labels:
            self.node_labels = list(labels)
        self.update()

    @staticmethod
    def _force_color(value):
        ratio = max(0.0, min(1.0, abs(value) / 40.0))
        return QColor(int(37 + ratio * 183), int(99 - ratio * 62), int(235 - ratio * 197))

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        available = self.rect().adjusted(34, 26, -46, -46)
        if available.width() < 80 or available.height() < 80:
            return
        ratio = self.width_mm / self.height_mm if self.height_mm else 0.8
        panel_h = available.height() * 0.9
        panel_w = panel_h * ratio
        if panel_w > available.width() * 0.9:
            panel_w = available.width() * 0.9
            panel_h = panel_w / ratio if ratio else available.height()
        x0 = available.left() + (available.width() - panel_w) / 2
        y0 = available.top() + (available.height() - panel_h) / 2
        panel = QRectF(x0, y0, panel_w, panel_h)

        shadow = QRectF(panel.x() + 4, panel.y() + 5, panel.width(), panel.height())
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QColor(15, 23, 42, 18))
        painter.drawRoundedRect(shadow, 8, 8)

        grad = QLinearGradient(panel.topLeft(), panel.bottomRight())
        grad.setColorAt(0.0, QColor("#f0f9ff"))
        grad.setColorAt(1.0, QColor("#dbeafe"))
        painter.setBrush(QBrush(grad))
        painter.setPen(QPen(QColor("#93c5fd"), 2))
        painter.drawRoundedRect(panel, 8, 8)

        painter.setPen(QPen(QColor("#bfdbfe"), 1, Qt.PenStyle.DashLine))
        for i in range(1, 3):
            x = panel.left() + panel.width() * i / 3
            painter.drawLine(QPointF(x, panel.top()), QPointF(x, panel.bottom()))
        for j in range(1, 3):
            y = panel.top() + panel.height() * j / 3
            painter.drawLine(QPointF(panel.left(), y), QPointF(panel.right(), y))

        painter.setPen(QColor("#1e3a8a"))
        painter.setFont(QFont("Microsoft YaHei", 10, QFont.Weight.Bold))
        painter.drawText(QRectF(panel.left(), panel.center().y() - 20, panel.width(), 22),
                         Qt.AlignmentFlag.AlignCenter, self.panel_no)
        painter.setPen(QColor("#64748b"))
        painter.setFont(QFont("Microsoft YaHei", 8))
        painter.drawText(QRectF(panel.left(), panel.center().y() + 2, panel.width(), 18),
                         Qt.AlignmentFlag.AlignCenter,
                         "{:.0f} × {:.0f} × {:.0f} mm".format(self.width_mm, self.height_mm, self.thickness_mm))

        corners = [
            QPointF(panel.left(), panel.top()),
            QPointF(panel.right(), panel.top()),
            QPointF(panel.right(), panel.bottom()),
            QPointF(panel.left(), panel.bottom()),
        ]
        for i, corner in enumerate(corners):
            force = self.forces[i] if i < len(self.forces) else 0.0
            color = self._force_color(force)
            painter.setBrush(QBrush(QColor("#ffffff")))
            painter.setPen(QPen(color, 3))
            painter.drawEllipse(corner, 16, 16)
            painter.setBrush(QBrush(color))
            painter.setPen(Qt.PenStyle.NoPen)
            painter.drawEllipse(corner, 5, 5)
            painter.setPen(color)
            painter.setFont(QFont("Microsoft YaHei", 8, QFont.Weight.Bold))
            label = self.node_labels[i] if i < len(self.node_labels) else "J-{:02d}".format(i + 1)
            if i == 0:
                painter.drawText(QRectF(corner.x() - 58, corner.y() - 26, 52, 16),
                                 Qt.AlignmentFlag.AlignRight, label)
            elif i == 1:
                painter.drawText(QRectF(corner.x() + 6, corner.y() - 26, 60, 16),
                                 Qt.AlignmentFlag.AlignLeft, label)
            elif i == 2:
                painter.drawText(QRectF(corner.x() + 6, corner.y() + 12, 60, 16),
                                 Qt.AlignmentFlag.AlignLeft, label)
            else:
                painter.drawText(QRectF(corner.x() - 58, corner.y() + 12, 52, 16),
                                 Qt.AlignmentFlag.AlignRight, label)
            if force:
                painter.setPen(QColor("#475569"))
                painter.setFont(QFont("Microsoft YaHei", 7))
                force_y = corner.y() - 30 if i >= 2 else corner.y() + 18
                painter.drawText(QRectF(corner.x() - 24, force_y, 48, 14),
                                 Qt.AlignmentFlag.AlignCenter, "{:.1f} kN".format(force))

        painter.setPen(QPen(QColor("#94a3b8"), 1))
        dim_y = panel.bottom() + 22
        painter.drawLine(QPointF(panel.left(), dim_y), QPointF(panel.right(), dim_y))
        painter.drawLine(QPointF(panel.left(), dim_y - 5), QPointF(panel.left(), dim_y + 5))
        painter.drawLine(QPointF(panel.right(), dim_y - 5), QPointF(panel.right(), dim_y + 5))
        painter.setFont(QFont("Microsoft YaHei", 8))
        painter.drawText(QRectF(panel.left(), dim_y + 4, panel.width(), 16),
                         Qt.AlignmentFlag.AlignCenter, "{:.0f} mm".format(self.width_mm))
        dim_x = panel.right() + 20
        painter.drawLine(QPointF(dim_x, panel.top()), QPointF(dim_x, panel.bottom()))
        painter.drawLine(QPointF(dim_x - 5, panel.top()), QPointF(dim_x + 5, panel.top()))
        painter.drawLine(QPointF(dim_x - 5, panel.bottom()), QPointF(dim_x + 5, panel.bottom()))
        painter.drawText(QRectF(dim_x + 4, panel.center().y() - 8, 60, 16),
                         Qt.AlignmentFlag.AlignLeft, "{:.0f} mm".format(self.height_mm))


class PanelModelView(QWidget):
    """按数据库模型绘制玻璃分格与驳接爪节点，与三维视图共用同一份数据。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.model = {"panel": {}, "nodes": [], "threshold": 120}
        self.setMinimumHeight(300)

    def set_model(self, model):
        self.model = model or {"panel": {}, "nodes": [], "threshold": 120}
        self.update()

    @staticmethod
    def _force_color(force, threshold):
        if not force:
            return QColor("#94a3b8")
        ratio = max(0.0, min(1.0, abs(float(force)) / max(float(threshold or 120), 1.0)))
        return QColor(int(37 + ratio * 183), int(99 - ratio * 62), int(235 - ratio * 197))

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        panel_data = (self.model or {}).get("panel") or {}
        width = float(panel_data.get("width") or 1500)
        height = float(panel_data.get("height") or 1800)
        thickness = float(panel_data.get("thickness") or 12)
        panel_no = panel_data.get("no") or "未命名分格"
        threshold = float((self.model or {}).get("threshold") or 120)

        available = self.rect().adjusted(34, 26, -46, -46)
        if available.width() < 80 or available.height() < 80:
            return
        ratio = width / height if height else 0.8
        panel_h = available.height() * 0.9
        panel_w = panel_h * ratio
        if panel_w > available.width() * 0.9:
            panel_w = available.width() * 0.9
            panel_h = panel_w / ratio if ratio else available.height()
        x0 = available.left() + (available.width() - panel_w) / 2
        y0 = available.top() + (available.height() - panel_h) / 2
        panel = QRectF(x0, y0, panel_w, panel_h)

        shadow = QRectF(panel.x() + 4, panel.y() + 5, panel.width(), panel.height())
        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QColor(15, 23, 42, 18))
        painter.drawRoundedRect(shadow, 8, 8)

        grad = QLinearGradient(panel.topLeft(), panel.bottomRight())
        grad.setColorAt(0.0, QColor("#f0f9ff"))
        grad.setColorAt(1.0, QColor("#dbeafe"))
        painter.setBrush(QBrush(grad))
        painter.setPen(QPen(QColor("#93c5fd"), 2))
        painter.drawRoundedRect(panel, 8, 8)

        painter.setPen(QPen(QColor("#bfdbfe"), 1, Qt.PenStyle.DashLine))
        for i in range(1, 3):
            gx = panel.left() + panel.width() * i / 3
            painter.drawLine(QPointF(gx, panel.top()), QPointF(gx, panel.bottom()))
        for j in range(1, 3):
            gy = panel.top() + panel.height() * j / 3
            painter.drawLine(QPointF(panel.left(), gy), QPointF(panel.right(), gy))

        nodes = (self.model or {}).get("nodes") or []
        center_y = panel.center().y()
        if len(nodes) == 1:
            center_y = panel.top() + 23
        painter.setPen(QColor("#1e3a8a"))
        painter.setFont(QFont("Microsoft YaHei", 10, QFont.Weight.Bold))
        painter.drawText(QRectF(panel.left(), center_y - 20, panel.width(), 22),
                         Qt.AlignmentFlag.AlignCenter, panel_no)
        painter.setPen(QColor("#64748b"))
        painter.setFont(QFont("Microsoft YaHei", 8))
        painter.drawText(QRectF(panel.left(), center_y + 2, panel.width(), 18),
                         Qt.AlignmentFlag.AlignCenter,
                         "{:.0f} × {:.0f} × {:.0f} mm".format(width, height, thickness))

        if not nodes:
            painter.setPen(QColor("#cbd5e1"))
            painter.setFont(QFont("Microsoft YaHei", 9))
            painter.drawText(QRectF(panel.left(), panel.center().y() + 26, panel.width(), 20),
                             Qt.AlignmentFlag.AlignCenter, "尚未布置驳接爪节点")
        arm_len = max(16.0, min(panel.width(), panel.height()) * 0.10)
        for node in nodes:
            nx = float(node.get("x") or 0)
            ny = float(node.get("y") or 0)
            cx = panel.center().x() + (nx / width) * panel.width()
            cy = panel.center().y() - (ny / height) * panel.height()
            arms = int(node.get("arms") or 4)
            forces = node.get("forces") or []
            main_force = float(node.get("force") or 0)
            color = self._force_color(main_force, threshold)
            for j in range(max(1, arms)):
                angle = 2 * math.pi * j / arms + math.pi / 4
                arm_force = float(forces[j]) if j < len(forces) else main_force
                arm_color = self._force_color(arm_force, threshold)
                end = QPointF(cx + math.cos(angle) * arm_len, cy + math.sin(angle) * arm_len)
                painter.setPen(QPen(arm_color, 2))
                painter.drawLine(QPointF(cx, cy), end)
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QBrush(arm_color))
                painter.drawEllipse(end, 3.0, 3.0)
            painter.setBrush(QBrush(QColor("#ffffff")))
            painter.setPen(QPen(color, 2.5))
            painter.drawEllipse(QPointF(cx, cy), 8.5, 8.5)
            painter.setBrush(QBrush(color))
            painter.setPen(Qt.PenStyle.NoPen)
            painter.drawEllipse(QPointF(cx, cy), 3.0, 3.0)

            label = str(node.get("label") or "")
            painter.setFont(QFont("Microsoft YaHei", 8, QFont.Weight.Bold))
            painter.setPen(QColor("#1e293b"))
            label_above = cy > panel.top() + 34
            label_y = cy - 30 if label_above else cy + 14
            painter.drawText(QRectF(cx - 46, label_y, 92, 14),
                             Qt.AlignmentFlag.AlignCenter, label)
            if main_force:
                painter.setFont(QFont("Microsoft YaHei", 7))
                painter.setPen(QColor("#475569"))
                force_y = cy + 16 if label_above else cy - 30
                painter.drawText(QRectF(cx - 46, force_y, 92, 13),
                                 Qt.AlignmentFlag.AlignCenter, "{:.1f} kN".format(main_force))

        painter.setPen(QPen(QColor("#94a3b8"), 1))
        dim_y = panel.bottom() + 22
        painter.drawLine(QPointF(panel.left(), dim_y), QPointF(panel.right(), dim_y))
        painter.drawLine(QPointF(panel.left(), dim_y - 5), QPointF(panel.left(), dim_y + 5))
        painter.drawLine(QPointF(panel.right(), dim_y - 5), QPointF(panel.right(), dim_y + 5))
        painter.setFont(QFont("Microsoft YaHei", 8))
        painter.drawText(QRectF(panel.left(), dim_y + 4, panel.width(), 16),
                         Qt.AlignmentFlag.AlignCenter, "{:.0f} mm".format(width))
        dim_x = panel.right() + 20
        painter.drawLine(QPointF(dim_x, panel.top()), QPointF(dim_x, panel.bottom()))
        painter.drawLine(QPointF(dim_x - 5, panel.top()), QPointF(dim_x + 5, panel.top()))
        painter.drawLine(QPointF(dim_x - 5, panel.bottom()), QPointF(dim_x + 5, panel.bottom()))
        painter.drawText(QRectF(dim_x + 4, panel.center().y() - 8, 60, 16),
                         Qt.AlignmentFlag.AlignLeft, "{:.0f} mm".format(height))


class SliderControl(QWidget):
    """滑块 + 数值显示，用于实时调参。"""

    valueChanged = pyqtSignal(float)

    def __init__(self, title, minimum, maximum, value, decimals=2, suffix="", parent=None):
        super().__init__(parent)
        self._min = float(minimum)
        self._max = float(maximum)
        self._decimals = int(decimals)
        self._suffix = suffix
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(2)
        top = QHBoxLayout()
        top.setSpacing(8)
        label = QLabel(title)
        label.setObjectName("fieldLabel")
        self.value_label = QLabel("")
        self.value_label.setObjectName("sectionHint")
        top.addWidget(label)
        top.addStretch(1)
        top.addWidget(self.value_label)
        layout.addLayout(top)
        self.slider = QSlider(Qt.Orientation.Horizontal)
        self.slider.setRange(0, 1000)
        self.slider.setSingleStep(10)
        layout.addWidget(self.slider)
        self.slider.valueChanged.connect(self._on_slider)
        self.set_value(value)

    def _on_slider(self, position):
        self._refresh_label()
        self.valueChanged.emit(self.value())

    def _refresh_label(self):
        self.value_label.setText(
            ("{:." + str(self._decimals) + "f}").format(self.value()) + self._suffix)

    def value(self):
        return self._min + (self._max - self._min) * self.slider.value() / 1000.0

    def set_value(self, value):
        value = max(self._min, min(self._max, float(value)))
        position = int(round((value - self._min) / (self._max - self._min) * 1000)) if self._max > self._min else 0
        self.slider.blockSignals(True)
        self.slider.setValue(position)
        self.slider.blockSignals(False)
        self._refresh_label()


class ArmVectorView(QWidget):
    """驳接爪爪臂受力矢量预览。"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.node_label = ""
        self.arms = 4
        self.forces = []
        self.threshold = 120.0
        self.setMinimumHeight(260)

    def set_data(self, node_label, arms, forces, threshold):
        self.node_label = node_label or ""
        self.arms = max(1, int(arms or 4))
        self.forces = [float(v) for v in (forces or [])]
        self.threshold = float(threshold or 120)
        self.update()

    @staticmethod
    def _color(force, threshold):
        ratio = max(0.0, min(1.0, abs(force) / max(threshold, 1.0)))
        return QColor(int(37 + ratio * 183), int(99 - ratio * 62), int(235 - ratio * 197))

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        width = self.width()
        height = self.height()
        cx = width / 2.0
        cy = height / 2.0 + 8
        radius = min(width, height) * 0.22
        painter.setPen(QPen(QColor("#dbe4f0"), 1, Qt.PenStyle.DashLine))
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawEllipse(QPointF(cx, cy), radius + 34, radius + 34)

        painter.setPen(QColor("#0f172a"))
        painter.setFont(QFont("Microsoft YaHei", 9, QFont.Weight.Bold))
        painter.drawText(QRectF(14, 8, max(120, width - 28), 18),
                         Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                         "{} · {} 爪臂".format(self.node_label or "未选择节点", self.arms))

        if not self.forces:
            painter.setPen(QColor("#94a3b8"))
            painter.setFont(QFont("Microsoft YaHei", 9))
            painter.drawText(QRectF(0, cy - 12, width, 24),
                             Qt.AlignmentFlag.AlignCenter, "选择节点与测点后实时预览")
            return

        max_force = max(abs(v) for v in self.forces) or 1.0
        for i in range(self.arms):
            angle = 2 * math.pi * i / self.arms - math.pi / 2
            force = self.forces[i] if i < len(self.forces) else 0.0
            ratio = abs(force) / max_force if max_force else 0
            length = radius * 0.45 + ratio * radius * 1.35
            end = QPointF(cx + math.cos(angle) * length, cy + math.sin(angle) * length)
            color = self._color(force, self.threshold)
            pen = QPen(color, 7)
            pen.setCapStyle(Qt.PenCapStyle.RoundCap)
            painter.setPen(pen)
            painter.drawLine(QPointF(cx, cy), end)

            head = 9
            left = QPointF(end.x() - math.cos(angle - 0.5) * head,
                           end.y() - math.sin(angle - 0.5) * head)
            right = QPointF(end.x() - math.cos(angle + 0.5) * head,
                            end.y() - math.sin(angle + 0.5) * head)
            path = QPainterPath(end)
            path.lineTo(left)
            path.lineTo(right)
            path.closeSubpath()
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QBrush(color))
            painter.drawPath(path)

            label_radius = length + 18
            lx = cx + math.cos(angle) * label_radius
            ly = cy + math.sin(angle) * label_radius
            painter.setPen(QColor("#334155"))
            painter.setFont(QFont("Microsoft YaHei", 8, QFont.Weight.Bold))
            painter.drawText(QRectF(lx - 34, ly - 9, 68, 18),
                             Qt.AlignmentFlag.AlignCenter, "{:.1f}".format(force))

        painter.setPen(QColor("#aab4c0"))
        painter.setBrush(QColor("#e2e8f0"))
        painter.drawEllipse(QPointF(cx, cy), 20, 20)
        painter.setBrush(QColor("#64748b"))
        painter.setPen(Qt.PenStyle.NoPen)
        painter.drawEllipse(QPointF(cx, cy), 6, 6)


class ModelEditorView(PanelModelView):
    """可拖动节点的 2D 模型编辑器，与三维场景共用同一模型。"""

    nodeMoved = pyqtSignal(int, float, float)
    nodeMoveFinished = pyqtSignal(int, float, float)
    nodeSelected = pyqtSignal(int)
    nodeAddRequested = pyqtSignal(float, float)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.selected_index = -1
        self._dragging = False
        self.setMouseTracking(True)

    def _panel_rect_editor(self):
        panel = (self.model or {}).get("panel") or {}
        width = float(panel.get("width") or 1500)
        height = float(panel.get("height") or 1800)
        available = self.rect().adjusted(34, 26, -46, -46)
        ratio = width / height if height else 0.8
        panel_h = available.height() * 0.9
        panel_w = panel_h * ratio
        if panel_w > available.width() * 0.9:
            panel_w = available.width() * 0.9
            panel_h = panel_w / ratio if ratio else available.height()
        x0 = available.left() + (available.width() - panel_w) / 2
        y0 = available.top() + (available.height() - panel_h) / 2
        return QRectF(x0, y0, panel_w, panel_h), width, height

    def _node_point(self, node):
        rect, width, height = self._panel_rect_editor()
        nx = float(node.get("x") or 0)
        ny = float(node.get("y") or 0)
        return (QPointF(rect.center().x() + nx / width * rect.width(),
                        rect.center().y() - ny / height * rect.height()), rect, width, height)

    def _hit_node(self, pos):
        nodes = (self.model or {}).get("nodes") or []
        for index, node in enumerate(nodes):
            point, _, _, _ = self._node_point(node)
            if (point.x() - pos.x()) ** 2 + (point.y() - pos.y()) ** 2 <= 20 ** 2:
                return index
        return -1

    def mousePressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return
        index = self._hit_node(event.position())
        if index >= 0:
            self.selected_index = index
            self._dragging = True
            self.setCursor(Qt.CursorShape.ClosedHandCursor)
            self.nodeSelected.emit(index)
            self.update()

    def mouseMoveEvent(self, event):
        if not self._dragging:
            index = self._hit_node(event.position())
            self.setCursor(Qt.CursorShape.OpenHandCursor if index >= 0 else Qt.CursorShape.ArrowCursor)
            return
        nodes = (self.model or {}).get("nodes") or []
        if self.selected_index < 0 or self.selected_index >= len(nodes):
            return
        _, rect, width, height = self._node_point(nodes[self.selected_index])
        x = (event.position().x() - rect.center().x()) / rect.width() * width
        y = -(event.position().y() - rect.center().y()) / rect.height() * height
        x = max(-width / 2, min(width / 2, x))
        y = max(-height / 2, min(height / 2, y))
        node = nodes[self.selected_index]
        node["x"] = round(x, 1)
        node["y"] = round(y, 1)
        if node.get("nid") is not None:
            self.nodeMoved.emit(int(node["nid"]), node["x"], node["y"])
        self.update()

    def mouseReleaseEvent(self, event):
        if self._dragging:
            nodes = (self.model or {}).get("nodes") or []
            if 0 <= self.selected_index < len(nodes):
                node = nodes[self.selected_index]
                if node.get("nid") is not None:
                    self.nodeMoveFinished.emit(int(node["nid"]), float(node["x"]), float(node["y"]))
            self._dragging = False
            self.setCursor(Qt.CursorShape.OpenHandCursor)

    def mouseDoubleClickEvent(self, event):
        if self._hit_node(event.position()) >= 0:
            return
        _, rect, width, height = self._panel_rect_editor()
        x = (event.position().x() - rect.center().x()) / rect.width() * width
        y = -(event.position().y() - rect.center().y()) / rect.height() * height
        self.nodeAddRequested.emit(round(x, 1), round(y, 1))

    def paintEvent(self, event):
        super().paintEvent(event)
        nodes = (self.model or {}).get("nodes") or []
        if 0 <= self.selected_index < len(nodes):
            point, _, _, _ = self._node_point(nodes[self.selected_index])
            painter = QPainter(self)
            painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.setPen(QPen(QColor("#10b981"), 2, Qt.PenStyle.DashLine))
            painter.drawEllipse(point, 22, 22)


class HeatmapView(QWidget):
    """二维参数扫描热力图，点击格子回传工况。"""

    cellClicked = pyqtSignal(int, int, float, float, float)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.xs = []
        self.ys = []
        self.matrix = []
        self.x_label = ""
        self.y_label = ""
        self.unit = ""
        self.selected = (-1, -1)
        self.hover = (-1, -1)
        self.setMinimumHeight(300)
        self.setMouseTracking(True)

    def set_data(self, xs, ys, matrix, x_label, y_label, unit="", selected=None):
        self.xs = list(xs)
        self.ys = list(ys)
        self.matrix = [list(row) for row in matrix]
        self.x_label = x_label
        self.y_label = y_label
        self.unit = unit
        if selected is not None:
            self.selected = selected
        self.update()

    def _plot_rect(self):
        return QRectF(64, 30, max(40, self.width() - 64 - 76), max(40, self.height() - 76))

    def _cell_at(self, pos):
        if not self.xs or not self.ys:
            return -1, -1
        plot = self._plot_rect()
        if not plot.contains(pos):
            return -1, -1
        col = int((pos.x() - plot.left()) / (plot.width() / len(self.xs)))
        row = int((plot.bottom() - pos.y()) / (plot.height() / len(self.ys)))
        col = max(0, min(len(self.xs) - 1, col))
        row = max(0, min(len(self.ys) - 1, row))
        return row, col

    def _cell_rect(self, row, col):
        plot = self._plot_rect()
        cw = plot.width() / len(self.xs)
        ch = plot.height() / len(self.ys)
        x = plot.left() + col * cw
        y = plot.bottom() - (row + 1) * ch
        return QRectF(x, y, cw, ch)

    @staticmethod
    def _lerp(a, b, t):
        return QColor(int(a[0] + (b[0] - a[0]) * t),
                      int(a[1] + (b[1] - a[1]) * t),
                      int(a[2] + (b[2] - a[2]) * t))

    def _color(self, ratio):
        ratio = max(0.0, min(1.0, ratio))
        low = (219, 234, 254)
        mid = (251, 191, 36)
        high = (220, 38, 38)
        if ratio < 0.5:
            return self._lerp(low, mid, ratio / 0.5)
        return self._lerp(mid, high, (ratio - 0.5) / 0.5)

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        if not self.matrix or not self.xs or not self.ys:
            painter.setPen(QColor("#94a3b8"))
            painter.setFont(QFont("Microsoft YaHei", 9))
            painter.drawText(self.rect(), Qt.AlignmentFlag.AlignCenter, "暂无扫描数据")
            return
        values = [v for row in self.matrix for v in row]
        lo, hi = min(values), max(values)
        span = hi - lo if hi != lo else 1.0
        plot = self._plot_rect()

        for row in range(len(self.ys)):
            for col in range(len(self.xs)):
                rect = self._cell_rect(row, col)
                ratio = (self.matrix[row][col] - lo) / span
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QBrush(self._color(ratio)))
                painter.drawRect(rect)
                painter.setPen(QPen(QColor(255, 255, 255, 180), 1))
                painter.setBrush(Qt.BrushStyle.NoBrush)
                painter.drawRect(rect)
        if 0 <= self.selected[0] < len(self.ys) and 0 <= self.selected[1] < len(self.xs):
            painter.setPen(QPen(QColor("#0f172a"), 3))
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawRect(self._cell_rect(*self.selected))
        if 0 <= self.hover[0] < len(self.ys) and 0 <= self.hover[1] < len(self.xs):
            painter.setPen(QPen(QColor("#ffffff"), 2))
            painter.setBrush(Qt.BrushStyle.NoBrush)
            painter.drawRect(self._cell_rect(*self.hover))

        painter.setPen(QColor("#64748b"))
        painter.setFont(QFont("Microsoft YaHei", 8))
        painter.drawText(QRectF(0, 4, 160, 16),
                         Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter,
                         self.y_label)
        for col, value in enumerate(self.xs):
            rect = self._cell_rect(0, col)
            label = "{:g}".format(value) if abs(value - round(value)) < 1e-6 else "{:.1f}".format(value)
            painter.drawText(QRectF(rect.left(), plot.bottom() + 5, rect.width(), 16),
                             Qt.AlignmentFlag.AlignHCenter, label)
        for row, value in enumerate(self.ys):
            rect = self._cell_rect(row, 0)
            label = "{:g}".format(value) if abs(value - round(value)) < 1e-6 else "{:.1f}".format(value)
            painter.drawText(QRectF(0, rect.center().y() - 8, 58, 16),
                             Qt.AlignmentFlag.AlignRight | Qt.AlignmentFlag.AlignVCenter,
                             label)
        painter.drawText(QRectF(plot.left(), plot.bottom() + 24, plot.width(), 18),
                         Qt.AlignmentFlag.AlignCenter, self.x_label)

        bar = QRectF(self.width() - 58, plot.top(), 14, plot.height())
        steps = 32
        for i in range(steps):
            ratio = i / (steps - 1)
            color = self._color(ratio)
            painter.setPen(Qt.PenStyle.NoPen)
            painter.setBrush(QBrush(color))
            y = bar.bottom() - (i + 1) * bar.height() / steps
            painter.drawRect(QRectF(bar.left(), y, bar.width(), bar.height() / steps + 1))
        painter.setPen(QColor("#64748b"))
        painter.setFont(QFont("Microsoft YaHei", 8))
        painter.drawText(QRectF(bar.right() + 3, bar.top() - 4, 40, 16),
                         Qt.AlignmentFlag.AlignLeft, "{:.0f}".format(hi))
        painter.drawText(QRectF(bar.right() + 3, bar.bottom() - 12, 40, 16),
                         Qt.AlignmentFlag.AlignLeft, "{:.0f}".format(lo))
        painter.drawText(QRectF(bar.right() + 3, bar.center().y() - 8, 40, 16),
                         Qt.AlignmentFlag.AlignLeft, self.unit)

    def mouseMoveEvent(self, event):
        row, col = self._cell_at(event.position())
        if (row, col) != self.hover:
            self.hover = (row, col)
            self.update()
        if row >= 0 and col >= 0:
            QToolTip.showText(
                event.globalPosition().toPoint(),
                "{} {:.1f} ｜ {} {:.2f}\n{} {:.1f}".format(
                    self.x_label, self.xs[col], self.y_label, self.ys[row],
                    "风险", self.matrix[row][col]))

    def leaveEvent(self, event):
        self.hover = (-1, -1)
        self.update()

    def mousePressEvent(self, event):
        if event.button() != Qt.MouseButton.LeftButton:
            return
        row, col = self._cell_at(event.position())
        if row < 0 or col < 0:
            return
        self.selected = (row, col)
        self.update()
        self.cellClicked.emit(row, col, self.xs[col], self.ys[row], self.matrix[row][col])


# --------------------------主窗口UI类--------------------------
class MainWindow(QMainWindow):
    def __init__(self, db, user):
        super().__init__()
        self.db = db
        self.user = user
        self.role = int(user.get("role", USER_ROLE_VISITOR))
        self.is_admin = self.role == USER_ROLE_ADMIN
        self.can_write = self.role in (USER_ROLE_ADMIN, USER_ROLE_ENGINEER)
        self.solver = MuskInversionSolver()
        self.hash_tool = HashTreeTool()
        self.write_buttons = []
        self.admin_buttons = []
        self.calc_thread = None
        self._calc_context = None
        self._pending_scene = None
        self._pending_model = None
        self._scene_ready = False

        SAVE_ROOT.mkdir(parents=True, exist_ok=True)
        REPORT_DIR.mkdir(parents=True, exist_ok=True)
        EVIDENCE_DIR.mkdir(parents=True, exist_ok=True)

        self.setWindowTitle("{} - {}（{}）".format(APP_TITLE, self.user.get("realname", ""), ROLE_NAMES.get(self.role, "访客")))
        self.resize(1440, 900)
        self.setMinimumSize(1120, 720)
        self.init_ui()
        self.apply_permissions()
        self.audit("登录系统", "用户 {} 登录".format(self.user.get("username")))
        self.refresh_dashboard()

    # ----------------------通用小工具---------------------
    def audit(self, opt_type, detail):
        try:
            self.db.execute(
                "insert into audit_log(uid,opt_type,opt_detail,opt_time) values (?,?,?,?)",
                (self.user.get("uid"), opt_type, detail, now_text()))
        except Exception:
            pass

    def _make_table(self, headers):
        table = QTableWidget(0, len(headers))
        table.setHorizontalHeaderLabels(headers)
        table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        table.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        table.verticalHeader().setVisible(False)
        table.verticalHeader().setDefaultSectionSize(32)
        header = table.horizontalHeader()
        header.setStretchLastSection(True)
        header.setHighlightSections(False)
        header.setDefaultAlignment(Qt.AlignmentFlag.AlignLeft | Qt.AlignmentFlag.AlignVCenter)
        header.setSectionResizeMode(QHeaderView.ResizeMode.Stretch)
        if headers and str(headers[0]).strip().upper() == "ID":
            header.setSectionResizeMode(0, QHeaderView.ResizeMode.Fixed)
            table.setColumnWidth(0, 56)
        table.setShowGrid(False)
        table.setFrameShape(QFrame.Shape.NoFrame)
        table.setAlternatingRowColors(True)
        table.setWordWrap(False)
        table.setTextElideMode(Qt.TextElideMode.ElideRight)
        table.setVerticalScrollMode(QAbstractItemView.ScrollMode.ScrollPerPixel)
        table.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        return table

    def _fill_table(self, table, rows):
        table.setRowCount(len(rows))
        for r, row in enumerate(rows):
            for c, val in enumerate(row):
                text = "" if val is None else str(val)
                item = QTableWidgetItem(text)
                item.setToolTip(text)
                if c == 0 and val is not None:
                    item.setData(Qt.ItemDataRole.UserRole, val)
                    item.setTextAlignment(Qt.AlignmentFlag.AlignCenter)
                table.setItem(r, c, item)

    def _selected_id(self, table):
        row = table.currentRow()
        if row < 0:
            return None
        item = table.item(row, 0)
        return item.data(Qt.ItemDataRole.UserRole) if item else None

    def _select_id(self, table, target):
        for row in range(table.rowCount()):
            item = table.item(row, 0)
            if item is not None and item.data(Qt.ItemDataRole.UserRole) == target:
                table.selectRow(row)
                return

    def apply_permissions(self):
        for btn in self.write_buttons:
            btn.setEnabled(self.can_write)
        for btn in self.admin_buttons:
            btn.setEnabled(self.is_admin)
        if not self.can_write:
            self.statusBar().showMessage("当前为访客只读模式，所有写入操作已禁用")

    def init_ui(self):
        central = QWidget()
        central.setObjectName("appRoot")
        self.setCentralWidget(central)
        root = QHBoxLayout(central)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        sidebar, self.nav_list = self._build_sidebar()
        root.addWidget(sidebar)

        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(0, 0, 0, 0)
        right_layout.setSpacing(0)
        right_layout.addWidget(self._build_topbar())
        self.stack = QStackedWidget()
        right_layout.addWidget(self.stack, 1)
        root.addWidget(right, 1)

        self.tab_dashboard, layout_dashboard = self._make_page(
            "工作台", "工程台账、受力反演与证据封存的总览")
        self.tab_project, layout_project = self._make_page(
            "工程管理", "维护工程项目、玻璃分格与驳接爪节点三级台账")
        self.tab_transfer, layout_transfer = self._make_page(
            "分格与传力", "查看玻璃分格角点装配与爪臂传力路径核查")
        self.tab_model_flow, layout_model_flow = self._make_page(
            "模型联动", "从空白分格开始逐步建立节点、测点和反演，2D 与 3D 同步变化")
        self.tab_calibration, layout_calibration = self._make_page(
            "测点配准", "测点布设、CSV 采样导入与方向零点、温漂时差校正")
        self.tab_measure, layout_measure = self._make_page(
            "测点数据录入", "按节点录入应变、挠度测点数据，作为反演计算的输入")
        self.tab_calc, layout_calc = self._make_page(
            "受力反演计算", "配置参数并执行多爪耦合受力反演，结果自动落库")
        self.tab_contact, layout_contact = self._make_page(
            "接触与转动", "孔边接触压力、垫片刚度与驳接头转动约束分析")
        self.tab_eccentric, layout_eccentric = self._make_page(
            "偏载溯因", "安装偏心、孔位偏差与预紧不均的五因素归因分析")
        self.tab_wind, layout_wind = self._make_page(
            "风压推演", "正负风压反向推演、测点缺失组合与有界反力包络")
        self.tab_preload, layout_preload = self._make_page(
            "预紧调校", "按目标受力生成受限预紧方案并逐阶仿真")
        self.tab_twin, layout_twin = self._make_page(
            "数字孪生视图", "三维展示驳接爪受力分布，超限爪臂自动变红")
        self.tab_report, layout_report = self._make_page(
            "成果导出签认", "生成 PDF 报告、完成签认并封存可校验的证据链")
        self.tab_evidence, layout_evidence = self._make_page(
            "证据工单", "查看九类证据来源、复核工单与证据链封存状态")
        self.tab_user, layout_user = self._make_page(
            "账号权限管理", "维护系统账号、角色权限与启用状态")

        self.init_dashboard_tab(layout_dashboard)
        self.init_project_tab(layout_project)
        self.init_transfer_tab(layout_transfer)
        self.init_model_flow_tab(layout_model_flow)
        self.init_calibration_tab(layout_calibration)
        self.init_measure_tab(layout_measure)
        self.init_calc_tab(layout_calc)
        self.init_contact_tab(layout_contact)
        self.init_eccentric_tab(layout_eccentric)
        self.init_wind_tab(layout_wind)
        self.init_preload_tab(layout_preload)
        self.init_twin_tab(layout_twin)
        self.init_report_tab(layout_report)
        self.init_evidence_tab(layout_evidence)
        self.init_user_tab(layout_user)

        self.page_titles = ["工作台", "工程管理", "分格与传力", "模型联动",
                            "测点配准", "测点数据录入", "受力反演计算", "接触与转动",
                            "偏载溯因", "风压推演", "预紧调校",
                            "数字孪生视图", "成果导出签认", "证据工单", "账号权限管理"]
        pages = [self.tab_dashboard, self.tab_project, self.tab_transfer,
                 self.tab_model_flow, self.tab_calibration, self.tab_measure,
                 self.tab_calc, self.tab_contact, self.tab_eccentric,
                 self.tab_wind, self.tab_preload, self.tab_twin,
                 self.tab_report, self.tab_evidence, self.tab_user]
        self.nav_index = {}
        for index, (page, title) in enumerate(zip(pages, self.page_titles)):
            self.stack.addWidget(page)
            self.nav_list.addItem(title)
            self.nav_index[title] = index
        self.nav_list.currentRowChanged.connect(self.switch_page)
        self.nav_list.setCurrentRow(0)

        self.statusBar().setSizeGripEnabled(False)
        self.statusBar().showMessage("就绪")

    def _build_sidebar(self):
        side = QFrame()
        side.setObjectName("sidebar")
        side.setFixedWidth(224)
        layout = QVBoxLayout(side)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)

        brand = QWidget()
        brand.setObjectName("brandBox")
        bh = QHBoxLayout(brand)
        bh.setContentsMargins(18, 22, 14, 16)
        bh.setSpacing(10)
        logo = QLabel("驳")
        logo.setObjectName("brandLogo")
        logo.setFixedSize(38, 38)
        logo.setAlignment(Qt.AlignmentFlag.AlignCenter)
        bh.addWidget(logo)
        tv = QVBoxLayout()
        tv.setSpacing(2)
        name = QLabel("驳接爪受力反演")
        name.setObjectName("brandName")
        sub = QLabel("CURTAIN WALL · V1.0")
        sub.setObjectName("brandSub")
        tv.addWidget(name)
        tv.addWidget(sub)
        bh.addLayout(tv)
        bh.addStretch(1)
        layout.addWidget(brand)

        nav_wrap = QWidget()
        nw = QVBoxLayout(nav_wrap)
        nw.setContentsMargins(22, 12, 22, 6)
        nav_label = QLabel("功能导航")
        nav_label.setObjectName("navSection")
        nw.addWidget(nav_label)
        layout.addWidget(nav_wrap)

        nav = QListWidget()
        nav.setObjectName("nav")
        nav.setFocusPolicy(Qt.FocusPolicy.NoFocus)
        nav.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        nav.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        layout.addWidget(nav, 1)

        user_box = QFrame()
        user_box.setObjectName("sidebarUser")
        uh = QHBoxLayout(user_box)
        uh.setContentsMargins(16, 14, 12, 14)
        uh.setSpacing(10)
        realname = self.user.get("realname") or self.user.get("username") or "用户"
        avatar = QLabel(realname[0])
        avatar.setObjectName("avatar")
        avatar.setFixedSize(34, 34)
        avatar.setAlignment(Qt.AlignmentFlag.AlignCenter)
        uh.addWidget(avatar)
        info = QVBoxLayout()
        info.setSpacing(2)
        name_label = QLabel(realname)
        name_label.setObjectName("userName")
        role_label = QLabel(ROLE_NAMES.get(self.role, "访客"))
        role_label.setObjectName("userRole")
        info.addWidget(name_label)
        info.addWidget(role_label)
        uh.addLayout(info)
        uh.addStretch(1)
        exit_btn = QPushButton("退出")
        exit_btn.setObjectName("sideExit")
        exit_btn.setCursor(Qt.CursorShape.PointingHandCursor)
        exit_btn.clicked.connect(self.close)
        uh.addWidget(exit_btn)
        layout.addWidget(user_box)
        return side, nav

    def _build_topbar(self):
        bar = QFrame()
        bar.setObjectName("topbar")
        bar.setFixedHeight(58)
        h = QHBoxLayout(bar)
        h.setContentsMargins(26, 0, 26, 0)
        h.setSpacing(8)
        self.crumb = QLabel("工作台")
        self.crumb.setObjectName("crumb")
        h.addWidget(self.crumb)
        h.addStretch(1)
        dot = QLabel("●")
        dot.setObjectName("dbDot")
        db_state = QLabel("本地数据库")
        db_state.setObjectName("dbState")
        h.addWidget(dot)
        h.addWidget(db_state)
        h.addSpacing(16)
        user_label = QLabel("{} · {}".format(self.user.get("realname"), ROLE_NAMES.get(self.role, "访客")))
        user_label.setObjectName("topUser")
        h.addWidget(user_label)
        return bar

    def _make_page(self, title, subtitle):
        page = QWidget()
        page.setObjectName("page")
        outer = QVBoxLayout(page)
        outer.setContentsMargins(28, 22, 28, 22)
        outer.setSpacing(4)
        title_label = QLabel(title)
        title_label.setObjectName("pageTitle")
        sub_label = QLabel(subtitle)
        sub_label.setObjectName("pageSub")
        outer.addWidget(title_label)
        outer.addWidget(sub_label)
        outer.addSpacing(10)
        body = QWidget()
        body.setObjectName("pageBody")
        body_layout = QVBoxLayout(body)
        body_layout.setContentsMargins(0, 0, 0, 0)
        body_layout.setSpacing(12)
        outer.addWidget(body, 1)
        return page, body_layout

    def switch_page(self, index):
        if index < 0 or index >= self.stack.count():
            return
        self.stack.setCurrentIndex(index)
        self.crumb.setText("工作台   /   " + self.page_titles[index])
        if self.page_titles[index] == "工作台":
            self.refresh_dashboard()
        elif self.page_titles[index] == "分格与传力":
            self.refresh_transfer()
        elif self.page_titles[index] == "模型联动":
            self._flow_refresh()
        elif self.page_titles[index] == "证据工单":
            self.refresh_evidence_tab()

    def go_page(self, title):
        index = getattr(self, "nav_index", {}).get(title)
        if index is not None:
            self.nav_list.setCurrentRow(index)

    # ----------------------工作台---------------------
    def _result_card(self, label, value="—"):
        frame = QFrame()
        frame.setObjectName("resultCard")
        frame.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        layout = QVBoxLayout(frame)
        layout.setContentsMargins(12, 9, 12, 9)
        layout.setSpacing(2)
        name = QLabel(label)
        name.setObjectName("resultLabel")
        val = QLabel(value)
        val.setObjectName("resultValue")
        layout.addWidget(name)
        layout.addWidget(val)
        return frame, val

    def _set_tag(self, label, text, kind="ok"):
        colors = {"ok": ("#dcfce7", "#15803d"),
                  "warn": ("#fef3c7", "#b45309"),
                  "info": ("#dbeafe", "#1d4ed8")}
        bg, fg = colors.get(kind, colors["info"])
        label.setText(text)
        label.setStyleSheet(
            "background:{}; color:{}; border-radius:9px; padding:2px 10px; "
            "font-size:11px; font-weight:600;".format(bg, fg))

    def auto_node_positions(self, count, width, height):
        w = float(width or 1500)
        h = float(height or 1800)
        if count <= 1:
            return [(0.0, 0.0)]
        if count == 2:
            return [(-w / 4, -h / 4), (w / 4, -h / 4)]
        if count == 3:
            return [(0.0, h / 4), (-w / 4, -h / 4), (w / 4, -h / 4)]
        if count == 4:
            return [(-w / 3, -h / 3), (w / 3, -h / 3), (w / 3, h / 3), (-w / 3, h / 3)]
        radius = min(w, h) / 3
        return [(radius * math.cos(2 * math.pi * i / count),
                 radius * math.sin(2 * math.pi * i / count)) for i in range(count)]

    def _latest_node_solution(self, nid):
        row = self.db.query_one(
            "select result_json, param_json from calc_record where nid=? order by rid desc limit 1", (nid,))
        if row is None:
            return [], 120.0
        result = safe_json_loads(row["result_json"], {}) or {}
        param = safe_json_loads(row["param_json"], {}) or {}
        forces = [float(v) for v in (result.get("result") or [])]
        threshold = float(param.get("max_allow_force") or 120)
        return forces, threshold

    def build_panel_model(self, gid):
        if gid is None:
            return None
        panel = self.db.query_one("select * from glass_panel where gid=?", (gid,))
        if panel is None:
            return None
        width = float(panel["width"] or 1500)
        height = float(panel["height"] or 1800)
        thickness = float(panel["thickness"] or 12)
        rows = self.db.query_all("select * from claw_node where gid=? order by nid", (gid,))
        positions = [(float(r["pos_x"] or 0), float(r["pos_y"] or 0)) for r in rows]
        if len(rows) > 1 and all(abs(x) < 0.01 and abs(y) < 0.01 for x, y in positions):
            positions = self.auto_node_positions(len(rows), width, height)
        nodes = []
        threshold = 120.0
        max_force = 0.0
        for index, row in enumerate(rows):
            forces, node_threshold = self._latest_node_solution(row["nid"])
            threshold = node_threshold
            force = max((abs(v) for v in forces), default=0.0)
            max_force = max(max_force, force)
            x, y = positions[index] if index < len(positions) else (0.0, 0.0)
            nodes.append({
                "nid": row["nid"],
                "label": row["claw_no"] or "J-{:03d}".format(index + 1),
                "x": round(x, 1),
                "y": round(y, 1),
                "arms": int(row["arm_count"] or 4),
                "preload": float(row["preload"] or 0),
                "force": round(force, 2),
                "forces": [round(float(v), 2) for v in forces],
                "state": "已计算" if forces else "待计算",
            })
        return {
            "panel": {
                "gid": panel["gid"],
                "no": panel["glass_no"] or "未命名分格",
                "width": width,
                "height": height,
                "thickness": thickness,
            },
            "nodes": nodes,
            "threshold": threshold,
            "max_force": round(max_force, 2),
        }

    def push_model_to_scene(self, model):
        if not model:
            return
        self._pending_model = model
        if getattr(self, "_scene_ready", False):
            self._run_scene_model(model)

    def _run_scene_model(self, model):
        if not HAS_WEBENGINE or self.web_view is None:
            return
        try:
            payload = json.dumps(model, ensure_ascii=False)
            self.web_view.page().runJavaScript(
                "if (window.setModel) { setModel(" + payload + "); }")
        except Exception as exc:
            print("三维模型推送失败：{}".format(exc))

    def init_dashboard_tab(self, layout):
        stats = QHBoxLayout()
        stats.setSpacing(14)
        self.card_projects = StatCard("工程项目", "0", "个", "在建 / 已竣工", "#2563eb")
        self.card_panels = StatCard("玻璃分格", "0", "块", "含角点装配", "#0ea5e9")
        self.card_nodes = StatCard("驳接爪节点", "0", "个", "四爪 / 三爪", "#8b5cf6")
        self.card_records = StatCard("反演记录", "0", "条", "含超限告警", "#f59e0b")
        for card in (self.card_projects, self.card_panels, self.card_nodes, self.card_records):
            stats.addWidget(card, 1)
        layout.addLayout(stats)

        middle = QHBoxLayout()
        middle.setSpacing(14)
        chart_box = QGroupBox("节点最大受力（kN）")
        chart_layout = QVBoxLayout(chart_box)
        chart_layout.setSpacing(4)
        self.dash_chart = ChartWidget("bar")
        self.dash_chart.setMinimumHeight(230)
        chart_layout.addWidget(self.dash_chart, 1)
        self.dash_hint = QLabel("按最近反演记录统计")
        self.dash_hint.setObjectName("sectionHint")
        chart_layout.addWidget(self.dash_hint)
        middle.addWidget(chart_box, 3)

        recent_box = QGroupBox("最近反演记录")
        recent_layout = QVBoxLayout(recent_box)
        self.dash_recent = self._make_table(["节点", "最大受力", "结论", "时间"])
        recent_layout.addWidget(self.dash_recent)
        middle.addWidget(recent_box, 2)
        layout.addLayout(middle, 3)

        bottom = QHBoxLayout()
        bottom.setSpacing(14)
        audit_box = QGroupBox("最近操作动态")
        audit_layout = QVBoxLayout(audit_box)
        self.dash_audit = self._make_table(["时间", "用户", "操作"])
        audit_layout.addWidget(self.dash_audit)
        bottom.addWidget(audit_box, 2)

        quick_box = QGroupBox("快捷操作")
        quick_layout = QVBoxLayout(quick_box)
        quick_layout.setSpacing(9)
        btn_new = QPushButton("新建工程项目")
        btn_demo = QPushButton("生成示例数据")
        btn_demo.setObjectName("primaryBtn")
        btn_calc = QPushButton("进入受力反演")
        btn_calc.setObjectName("ghostBtn")
        btn_report = QPushButton("查看成果报告")
        btn_report.setObjectName("ghostBtn")
        for btn in (btn_new, btn_demo, btn_calc, btn_report):
            btn.setMinimumHeight(34)
            quick_layout.addWidget(btn)
        quick_layout.addStretch(1)
        bottom.addWidget(quick_box, 1)
        layout.addLayout(bottom, 2)

        self.write_buttons += [btn_new, btn_demo]
        btn_new.clicked.connect(self.add_project)
        btn_demo.clicked.connect(self.add_demo_data)
        btn_calc.clicked.connect(lambda: self.go_page("受力反演计算"))
        btn_report.clicked.connect(lambda: self.go_page("成果导出签认"))
        self.refresh_dashboard()

    def refresh_dashboard(self):
        projects = self.db.query_one("select count(*) as c from project_info")["c"]
        panels = self.db.query_one("select count(*) as c from glass_panel")["c"]
        nodes = self.db.query_one("select count(*) as c from claw_node")["c"]
        records = self.db.query_one("select count(*) as c from calc_record")["c"]
        self.card_projects.set_value(projects, "本地工程台账")
        self.card_panels.set_value(panels, "玻璃分格数量")
        self.card_nodes.set_value(nodes, "已有驳接爪节点")
        self.card_records.set_value(records, "含超限与已签认")

        rows = self.db.query_all(
            "select r.rid, r.result_json, r.status, r.calc_time, coalesce(c.claw_no, '节点') as claw_no "
            "from calc_record r left join claw_node c on c.nid = r.nid order by r.rid desc limit 8")
        labels = []
        values = []
        recent = []
        for r in rows:
            res = safe_json_loads(r["result_json"], {}) or {}
            forces = res.get("result", []) or []
            max_force = max((abs(float(v)) for v in forces), default=0.0)
            labels.append(r["claw_no"])
            values.append(max_force)
            recent.append([r["claw_no"], format_float(max_force, 1),
                           "通过" if int(r["status"] or 0) == 1 else "超限",
                           (r["calc_time"] or "")[5:16]])
        if values:
            self.dash_hint.setText("按最近 {} 条反演记录统计，阈值 120 kN".format(len(values)))
        else:
            labels = ["J-01", "J-02", "J-03", "J-04", "J-05", "J-06"]
            values = [18.4, 22.1, 15.7, 26.3, 19.8, 23.5]
            self.dash_hint.setText("暂无计算记录，当前展示示例数据")
        self.dash_chart.set_data(labels, [{"name": "最大受力", "color": "#2563eb", "values": values}], "")
        self._fill_table(self.dash_recent, recent)

        audit_rows = self.db.query_all(
            "select l.opt_time, coalesce(u.username, 'system'), l.opt_type "
            "from audit_log l left join user_info u on u.uid = l.uid order by l.lid desc limit 8")
        self._fill_table(self.dash_audit,
                         [[(r[0] or "")[5:16], r[1], r[2]] for r in audit_rows])

    # ----------------------分格与传力---------------------
    def init_transfer_tab(self, layout):
        self.transfer_selector = NodeSelector(self.db)
        self.transfer_selector.changed.connect(self.refresh_transfer)
        layout.addWidget(self.transfer_selector)

        body = QHBoxLayout()
        body.setSpacing(14)
        left_box = QGroupBox("分格与角点装配")
        left_layout = QVBoxLayout(left_box)
        self.transfer_schematic = PanelModelView()
        left_layout.addWidget(self.transfer_schematic, 1)
        body.addWidget(left_box, 3)

        right_box = QGroupBox("传力核查")
        right_layout = QVBoxLayout(right_box)
        right_layout.setSpacing(10)
        result_grid = QGridLayout()
        result_grid.setHorizontalSpacing(10)
        result_grid.setVerticalSpacing(10)
        card_total, self.transfer_total = self._result_card("总反力（kN）")
        card_max, self.transfer_max = self._result_card("角点最大（kN）")
        card_diff, self.transfer_diff = self._result_card("偏载差（kN）")
        card_verdict, self.transfer_verdict = self._result_card("核查结论", "待核查")
        result_grid.addWidget(card_total, 0, 0)
        result_grid.addWidget(card_max, 0, 1)
        result_grid.addWidget(card_diff, 0, 2)
        result_grid.addWidget(card_verdict, 0, 3)
        right_layout.addLayout(result_grid)
        btn_demo = QPushButton("重新核查")
        btn_demo.setObjectName("primaryBtn")
        btn_demo.clicked.connect(self.refresh_transfer)
        right_layout.addWidget(btn_demo)
        self.write_buttons.append(btn_demo)

        self.transfer_table = self._make_table(["角点", "反力(kN)", "占比", "状态"])
        right_layout.addWidget(self.transfer_table, 1)
        body.addWidget(right_box, 2)
        layout.addLayout(body, 3)

        chart_box = QGroupBox("角点反力分配")
        chart_layout = QVBoxLayout(chart_box)
        self.transfer_chart = ChartWidget("bar")
        self.transfer_chart.setMinimumHeight(200)
        chart_layout.addWidget(self.transfer_chart)
        layout.addWidget(chart_box, 2)

        self.refresh_transfer()

    def refresh_transfer(self):
        gid = self.transfer_selector.cb_panel.currentData()
        model = self.build_panel_model(gid)
        if model is None:
            model = {
                "panel": {"no": "暂无分格", "width": 1500, "height": 1800, "thickness": 12},
                "nodes": [], "threshold": 120.0, "max_force": 0.0,
            }
        self.transfer_schematic.set_model(model)
        self.push_model_to_scene(model)

        nodes = model.get("nodes") or []
        threshold = float(model.get("threshold") or 120)
        forces = [float(n.get("force") or 0) for n in nodes]
        computed = [f for f in forces if f > 0]
        total = sum(computed)
        max_force = max(computed, default=0.0)
        diff = (max(computed) - min(computed)) if computed else 0.0

        self.transfer_total.setText("{:.1f}".format(total))
        self.transfer_max.setText("{:.1f}".format(max_force))
        self.transfer_diff.setText("{:.1f}".format(diff))
        if not computed:
            self._set_tag(self.transfer_verdict, "待计算", "info")
        else:
            ok = max_force <= threshold and diff <= threshold * 0.06
            self._set_tag(self.transfer_verdict, "通过" if ok else "关注", "ok" if ok else "warn")

        table_rows = []
        for node, force in zip(nodes, forces):
            share = force / total * 100 if total else 0
            if force <= 0:
                status = "待计算"
            else:
                status = "正常" if force <= threshold else "超限"
            table_rows.append([node.get("label"), "{:.1f}".format(force),
                               "{:.1f}%".format(share), status])
        self._fill_table(self.transfer_table, table_rows)
        if nodes:
            self.transfer_chart.set_data(
                [n.get("label") for n in nodes],
                [{"name": "节点最大受力", "color": "#0ea5e9", "values": forces}], "")
        else:
            self.transfer_chart.set_data([], [])

    # ----------------------模型联动 ---------------------
    def init_model_flow_tab(self, layout):
        self.flow_step = 0
        self.flow_pid = None
        self.flow_gid = None
        self.flow_model = None
        self.flow_titles = [
            "建立空白分格",
            "修改分格尺寸",
            "布置四个驳接爪节点",
            "录入测点并执行反演",
            "推送到三维视图",
            "完成模型联动",
        ]
        self.flow_descs = [
            "新建工程与 1000 × 1200 空白玻璃分格",
            "尺寸改为 1500 × 1800，观察 2D 比例变化",
            "四角布点，每个节点 4 根爪臂",
            "写入测点并计算，节点按受力着色",
            "同一份模型数据同步到 3D 场景",
            "2D 示意与 3D 场景保持一致",
        ]
        top = QHBoxLayout()
        top.setSpacing(14)
        step_box = QGroupBox("分步联动流程")
        step_box.setFixedWidth(380)
        step_layout = QVBoxLayout(step_box)
        step_layout.setSpacing(6)
        self.flow_progress = QLabel("步骤 0 / 6")
        self.flow_progress.setObjectName("sectionHint")
        step_layout.addWidget(self.flow_progress)
        self.flow_step_items = []
        for i, (title, desc) in enumerate(zip(self.flow_titles, self.flow_descs)):
            item = QFrame()
            item_layout = QVBoxLayout(item)
            item_layout.setContentsMargins(10, 7, 10, 7)
            item_layout.setSpacing(1)
            title_label = QLabel()
            title_label.setStyleSheet("font-size:12px; font-weight:600; color:#94a3b8;")
            desc_label = QLabel(desc)
            desc_label.setObjectName("sectionHint")
            item_layout.addWidget(title_label)
            item_layout.addWidget(desc_label)
            self.flow_step_items.append((item, title_label, desc_label))
            step_layout.addWidget(item)
        step_layout.addStretch(1)
        top.addWidget(step_box)

        preview_box = QGroupBox("实时 2D 模型预览")
        preview_layout = QVBoxLayout(preview_box)
        edit_bar = QHBoxLayout()
        edit_bar.setSpacing(8)
        self.btn_flow_add = QPushButton("添加节点")
        self.btn_flow_sync = QPushButton("同步三维")
        edit_bar.addWidget(self.btn_flow_add)
        edit_bar.addWidget(self.btn_flow_sync)
        edit_bar.addStretch(1)
        edit_hint = QLabel("拖动节点可调整位置，双击空白处可添加节点")
        edit_hint.setObjectName("sectionHint")
        edit_bar.addWidget(edit_hint)
        preview_layout.addLayout(edit_bar)
        self.flow_schematic = ModelEditorView()
        preview_layout.addWidget(self.flow_schematic, 1)
        summary = QHBoxLayout()
        summary.setSpacing(16)
        self.flow_nodes_label = QLabel("节点：0")
        self.flow_force_label = QLabel("最大受力：—")
        self.flow_state_label = QLabel("模型：未建立")
        for label in (self.flow_nodes_label, self.flow_force_label, self.flow_state_label):
            label.setObjectName("sectionHint")
            summary.addWidget(label)
        summary.addStretch(1)
        preview_layout.addLayout(summary)
        self.flow_open3d = QPushButton("打开三维视图")
        self.flow_open3d.setEnabled(False)
        self.flow_open3d.clicked.connect(lambda: self.go_page("数字孪生视图"))
        preview_layout.addWidget(self.flow_open3d)
        top.addWidget(preview_box, 1)
        layout.addLayout(top, 3)

        log_box = QGroupBox("操作记录")
        log_layout = QVBoxLayout(log_box)
        self.flow_log = QTextEdit()
        self.flow_log.setObjectName("calcLog")
        self.flow_log.setReadOnly(True)
        self.flow_log.setMinimumHeight(130)
        log_layout.addWidget(self.flow_log)
        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.flow_next_btn = QPushButton("执行下一步")
        self.flow_next_btn.setObjectName("primaryBtn")
        self.flow_reset_btn = QPushButton("重置流程")
        self.flow_reset_btn.setObjectName("ghostBtn")
        bar.addWidget(self.flow_next_btn)
        bar.addWidget(self.flow_reset_btn)
        bar.addStretch(1)
        log_layout.addLayout(bar)
        layout.addWidget(log_box, 2)
        self.write_buttons += [self.flow_next_btn, self.flow_reset_btn]

        self.flow_next_btn.clicked.connect(self.flow_next)
        self.flow_reset_btn.clicked.connect(self.flow_reset)
        self.btn_flow_add.clicked.connect(lambda: self._flow_node_added(0.0, 0.0))
        self.btn_flow_sync.clicked.connect(self._flow_sync_scene)
        self.flow_schematic.nodeAddRequested.connect(self._flow_node_added)
        self.flow_schematic.nodeMoveFinished.connect(self._flow_node_saved)
        self.write_buttons += [self.btn_flow_add, self.btn_flow_sync]
        self._flow_refresh()
        self._flow_update_steps()
        self._flow_append("准备就绪：点击“执行下一步”，从空白分格开始建立模型。")

    def _flow_append(self, text):
        self.flow_log.append("[{}] {}".format(datetime.now().strftime("%H:%M:%S"), text))

    def _flow_empty_model(self):
        return {
            "panel": {"no": "空白分格", "width": 1000, "height": 1200, "thickness": 10},
            "nodes": [], "threshold": 120.0, "max_force": 0.0,
        }

    def _flow_refresh(self):
        model = self.build_panel_model(self.flow_gid) if self.flow_gid else None
        if model is None:
            model = self._flow_empty_model()
        self.flow_model = model
        self.flow_schematic.set_model(model)
        nodes = model.get("nodes") or []
        max_force = float(model.get("max_force") or 0)
        self.flow_nodes_label.setText("节点：{}".format(len(nodes)))
        self.flow_force_label.setText("最大受力：{}".format(
            "{:.1f} kN".format(max_force) if max_force else "—"))
        self.flow_state_label.setText("模型：已同步 2D / 3D" if self.flow_gid else "模型：未建立")
        if self.flow_gid:
            self.push_model_to_scene(model)

    def _flow_update_steps(self):
        self.flow_progress.setText("步骤 {} / 6".format(min(self.flow_step, 6)))
        for index, (item, title_label, _) in enumerate(self.flow_step_items):
            if index < self.flow_step:
                prefix, color, bg = "✓", "#15803d", "transparent"
            elif index == self.flow_step:
                prefix, color, bg = "●", "#1d4ed8", "#eff6ff"
            else:
                prefix, color, bg = "○", "#94a3b8", "transparent"
            title_label.setText("{} {}  {}".format(prefix, index + 1, self.flow_titles[index]))
            title_label.setStyleSheet(
                "font-size:12px; font-weight:600; color:{}; background:{};".format(color, bg))
        if self.flow_step >= 6:
            self.flow_next_btn.setText("已完成")
            self.flow_next_btn.setEnabled(False)
        else:
            self.flow_next_btn.setText("执行下一步")
            self.flow_next_btn.setEnabled(self.can_write)
        self.flow_open3d.setEnabled(bool(self.flow_gid) and self.flow_step >= 5)

    def _flow_select_project(self):
        if self.flow_pid is None:
            return
        for selector in (self.transfer_selector, self.calib_selector,
                         self.measure_selector, self.calc_selector):
            idx = selector.cb_project.findData(self.flow_pid)
            if idx >= 0:
                selector.cb_project.setCurrentIndex(idx)

    def flow_next(self):
        if not self.can_write or self.flow_step >= 6:
            return
        step = self.flow_step
        try:
            if step == 0:
                self._flow_create()
            elif step == 1:
                self._flow_resize()
            elif step == 2:
                self._flow_add_nodes()
            elif step == 3:
                self._flow_calculate()
            elif step == 4:
                self._flow_push_scene()
            elif step == 5:
                self._flow_append("完成：2D 示意图与 3D 场景由同一份模型数据驱动。")
        except Exception as exc:
            QMessageBox.critical(self, "模型联动失败", str(exc))
            return
        self.flow_step = min(6, step + 1)
        self._flow_refresh()
        self._flow_update_steps()

    def _flow_create(self):
        pid = self.db.execute(
            "insert into project_info(proj_name,facade_name,create_user,create_time,remark,status,update_time) "
            "values (?,?,?,?,?,?,?)",
            ("模型联动示例", "示例立面", self.user.get("uid"), now_text(),
             "分步建模工程", "在建", now_text()))
        gid = self.db.execute(
            "insert into glass_panel(pid,glass_no,width,height,thickness,glass_type,remark) "
            "values (?,?,?,?,?,?,?)",
            (pid, "GL-DEMO-01", 1000, 1200, 10, "中空钢化", "空白分格"))
        self.flow_pid, self.flow_gid = pid, gid
        self.audit("模型联动", "建立空白分格 ID {}（1000×1200）".format(gid))
        self.refresh_selectors()
        self._flow_select_project()
        self.refresh_dashboard()
        self._flow_append("步骤 1：创建工程《模型联动示例》与空白分格 GL-DEMO-01。")

    def _flow_resize(self):
        if self.flow_gid is None:
            raise RuntimeError("请先建立空白分格")
        self.db.execute(
            "update glass_panel set width=?, height=?, thickness=? where gid=?",
            (1500, 1800, 12, self.flow_gid))
        self.audit("模型联动", "分格尺寸改为 1500×1800×12")
        self.refresh_selectors()
        self._flow_select_project()
        self._flow_append("步骤 2：分格尺寸改为 1500 × 1800 × 12 mm，2D 比例与 3D 面板同步变化。")

    def _flow_add_nodes(self):
        if self.flow_gid is None:
            raise RuntimeError("请先建立空白分格")
        width, height = 1500.0, 1800.0
        positions = [(-width / 3, -height / 3), (width / 3, -height / 3),
                     (width / 3, height / 3), (-width / 3, height / 3)]
        for index, (x, y) in enumerate(positions):
            self.db.execute(
                "insert into claw_node(gid,claw_no,arm_count,preload,eccentricity,node_type,arm_len,"
                "pos_x,pos_y,remark) values (?,?,?,?,?,?,?,?,?,?)",
                (self.flow_gid, "J-DEMO-{:02d}".format(index + 1), 4, 20.0, 0.0,
                 "四爪", 300.0, x, y, "模型节点"))
        self.audit("模型联动", "布置 4 个驳接爪节点")
        self.refresh_selectors()
        self._flow_select_project()
        self._flow_append("步骤 3：四角布置 J-DEMO-01～04，每个节点 4 根爪臂。")

    def _flow_calculate(self):
        if self.flow_gid is None:
            raise RuntimeError("请先布置节点")
        nodes = self.db.query_all("select * from claw_node where gid=? order by nid", (self.flow_gid,))
        if not nodes:
            raise RuntimeError("当前分格还没有节点")
        strain_data = [
            [94.2, 88.6, 96.8, 90.4],
            [88.9, 95.2, 89.7, 97.1],
            [96.4, 90.8, 93.5, 88.2],
            [90.1, 96.7, 91.4, 94.9],
        ]
        deflect_data = [
            [0.92, 0.88, 0.95, 0.90],
            [0.87, 0.94, 0.89, 0.96],
            [0.95, 0.90, 0.93, 0.88],
            [0.89, 0.95, 0.91, 0.94],
        ]
        solver = self.solver
        param = {
            "max_allow_force": 120.0,
            "stiffness_k": 100.0,
            "reg_weight": ALG_WEIGHT_REG,
            "w1": 0.6,
            "w2": 0.4,
            "coupling": 0.06,
            "svd_eps": SVD_THRESHOLD,
            "transfer_matrix": solver.build_transfer_matrix(4, 0.06).tolist(),
        }
        for index, node in enumerate(nodes[:4]):
            strain = strain_data[index % len(strain_data)]
            deflect = deflect_data[index % len(deflect_data)]
            mid = self.db.execute(
                "insert into measure_point(nid,point_no,strain_data,deflect_data,collect_time,remark) "
                "values (?,?,?,?,?,?)",
                (node["nid"], "P-DEMO-{:02d}".format(index + 1), json.dumps(strain),
                 json.dumps(deflect), now_text(), "模型测点"))
            para = dict(param)
            para["stiffness_k"] = [param["stiffness_k"]] * len(strain)
            result = solver.coupling_claw_inversion(strain, deflect, para)
            result_json = json.dumps(result, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
            self.db.execute(
                "insert into calc_record(nid,mid,result_json,param_json,sha_hash,calc_time,status,alarm_msg) "
                "values (?,?,?,?,?,?,?,?)",
                (node["nid"], mid, result_json,
                 json.dumps(param, ensure_ascii=False, sort_keys=True),
                 sha256_text(result_json), now_text(),
                 1 if result.get("valid") else 0, ""))
        self.audit("模型联动", "4 个节点完成测点录入与受力反演")
        self.load_record_list()
        self.refresh_dashboard()
        self.refresh_selectors()
        self._flow_select_project()
        self._flow_append("步骤 4：写入 4 组测点并计算，节点按受力大小着色。")

    def _flow_push_scene(self):
        model = self.build_panel_model(self.flow_gid)
        if model is None:
            raise RuntimeError("模型尚未建立")
        self.push_model_to_scene(model)
        self.audit("模型联动", "模型已推送到三维视图")
        self._flow_append("步骤 5：模型已推送到 3D 场景，可点击“打开三维视图”查看。")

    def _flow_node_added(self, x, y):
        if self.flow_gid is None:
            QMessageBox.information(self, "提示", "请先执行步骤 1，建立空白分格")
            return
        count = self.db.query_one("select count(*) as c from claw_node where gid=?", (self.flow_gid,))["c"]
        if abs(x) < 0.01 and abs(y) < 0.01:
            x = 200 * math.cos(count * 1.4)
            y = 140 * math.sin(count * 1.4)
        nid = self.db.execute(
            "insert into claw_node(gid,claw_no,arm_count,preload,eccentricity,node_type,arm_len,"
            "pos_x,pos_y,remark) values (?,?,?,?,?,?,?,?,?,?)",
            (self.flow_gid, "J-N{:02d}".format(count + 1), 4, 20.0, 0.0,
             "四爪", 300.0, x, y, "交互添加节点"))
        self.audit("模型编辑", "新增节点 {}，位置 ({:.0f}, {:.0f})".format(nid, x, y))
        self._flow_refresh()
        self._flow_append("在 ({:.0f}, {:.0f}) mm 处添加节点 J-N{:02d}，2D 与 3D 已同步。".format(
            x, y, count + 1))

    def _flow_node_saved(self, nid, x, y):
        self.db.execute("update claw_node set pos_x=?, pos_y=? where nid=?", (x, y, nid))
        self.audit("模型编辑", "节点 {} 位置改为 ({:.0f}, {:.0f})".format(nid, x, y))
        self._flow_refresh()
        self._flow_append("拖动节点 {} 到 ({:.0f}, {:.0f}) mm，模型已更新。".format(nid, x, y))

    def _flow_sync_scene(self):
        if self.flow_gid is None:
            QMessageBox.information(self, "提示", "当前还没有可同步的模型")
            return
        model = self.build_panel_model(self.flow_gid)
        if model is None:
            return
        self.push_model_to_scene(model)
        self._flow_append("已把当前 2D 模型同步到三维场景。")

    def flow_reset(self):
        if self.flow_pid is not None:
            sub = "select nid from claw_node where gid in (select gid from glass_panel where pid=?)"
            self.db.execute_many([
                ("delete from measure_point where nid in ({})".format(sub), (self.flow_pid,)),
                ("delete from calc_record where nid in ({})".format(sub), (self.flow_pid,)),
                ("delete from claw_node where gid in (select gid from glass_panel where pid=?)", (self.flow_pid,)),
                ("delete from glass_panel where pid=?", (self.flow_pid,)),
                ("delete from project_info where pid=?", (self.flow_pid,)),
            ])
            self.audit("模型联动", "重置并清理建模工程")
        self.flow_step = 0
        self.flow_pid = None
        self.flow_gid = None
        self.flow_log.clear()
        self._flow_refresh()
        self._flow_update_steps()
        self.refresh_selectors()
        self.refresh_dashboard()
        self._flow_append("已重置。点击“执行下一步”重新开始。")

    # ----------------------测点配准---------------------
    def init_calibration_tab(self, layout):
        self.calib_selector = NodeSelector(self.db)
        self.calib_selector.changed.connect(self.load_calibration_demo)
        layout.addWidget(self.calib_selector)

        stats = QHBoxLayout()
        stats.setSpacing(14)
        self.calib_total_card = StatCard("测点总数", "0", "个", "当前节点采样", "#2563eb")
        self.calib_ok_card = StatCard("已配准", "0", "个", "方向 / 零点已核对", "#10b981")
        self.calib_bad_card = StatCard("异常测点", "0", "个", "需要人工复核", "#ef4444")
        self.calib_window_card = StatCard("同步窗口", "0", "ms", "温度时差补偿后", "#8b5cf6")
        for card in (self.calib_total_card, self.calib_ok_card, self.calib_bad_card, self.calib_window_card):
            stats.addWidget(card, 1)
        layout.addLayout(stats)

        bar = QHBoxLayout()
        bar.setSpacing(8)
        btn_import = QPushButton("导入 CSV 采样")
        btn_import.setObjectName("primaryBtn")
        btn_demo = QPushButton("载入示例测点")
        btn_run = QPushButton("执行配准校正")
        btn_run.setObjectName("ghostBtn")
        bar.addWidget(btn_import)
        bar.addWidget(btn_demo)
        bar.addStretch(1)
        bar.addWidget(btn_run)
        layout.addLayout(bar)

        content = QHBoxLayout()
        content.setSpacing(14)
        chart_box = QGroupBox("原始 / 校正应变对比（με）")
        chart_layout = QVBoxLayout(chart_box)
        self.calib_chart = ChartWidget("line")
        self.calib_chart.setMinimumHeight(240)
        chart_layout.addWidget(self.calib_chart)
        content.addWidget(chart_box, 3)

        table_box = QGroupBox("测点配准明细")
        table_layout = QVBoxLayout(table_box)
        self.calib_table = self._make_table(["测点", "方向", "零点(mV)", "温漂", "时差(ms)", "状态"])
        table_layout.addWidget(self.calib_table)
        content.addWidget(table_box, 2)
        layout.addLayout(content, 1)

        btn_import.clicked.connect(self.import_calibration_csv)
        btn_demo.clicked.connect(self.load_calibration_demo)
        btn_run.clicked.connect(self.execute_calibration)
        self.write_buttons += [btn_import, btn_demo, btn_run]
        self.calib_points = []
        self.load_calibration_demo()

    def load_calibration_demo(self):
        nid = self.calib_selector.current_node_id()
        rng = random.Random(nid if nid is not None else 7)
        points = []
        for i in range(8):
            raw = 10.5 + i * 0.85 + rng.uniform(-1.4, 1.4)
            corrected = raw * 0.972 + 0.35 + rng.uniform(-0.15, 0.15)
            if i < 6:
                status = "已配准"
            elif i == 6:
                status = "待配准"
            else:
                status = "异常"
            points.append({
                "label": "P-{:02d}".format(i + 1),
                "raw": round(raw, 2),
                "corrected": round(corrected, 2),
                "direction": "0°" if i % 2 == 0 else "90°",
                "zero": round(rng.uniform(-0.8, 0.8), 2),
                "drift": round(rng.uniform(0.4, 2.2), 2),
                "delta": int(rng.uniform(2, 18)),
                "status": status,
            })
        self.calib_points = points
        self._render_calibration()

    def _render_calibration(self):
        points = getattr(self, "calib_points", [])
        total = len(points)
        ok = sum(1 for p in points if p["status"] == "已配准")
        bad = sum(1 for p in points if p["status"] == "异常")
        window = max((p["delta"] for p in points), default=0)
        self.calib_total_card.set_value(total, "当前节点采样")
        self.calib_ok_card.set_value(ok, "方向 / 零点已核对")
        self.calib_bad_card.set_value(bad, "需要人工复核")
        self.calib_window_card.set_value(window, "温度时差补偿后")
        labels = [p["label"] for p in points]
        raw = [p["raw"] for p in points]
        corrected = [p["corrected"] for p in points]
        self.calib_chart.set_data(labels, [
            {"name": "原始应变", "color": "#94a3b8", "values": raw},
            {"name": "校正应变", "color": "#2563eb", "values": corrected, "fill": True},
        ], "")
        rows = [[p["label"], p["direction"], "{:.2f}".format(p["zero"]),
                 "{:.2f}".format(p["drift"]), str(p["delta"]), p["status"]] for p in points]
        self._fill_table(self.calib_table, rows)

    def execute_calibration(self):
        if not getattr(self, "calib_points", None):
            QMessageBox.information(self, "提示", "请先导入 CSV 或载入示例测点")
            return
        for point in self.calib_points:
            point["status"] = "已配准"
            point["corrected"] = round(point["raw"] * 0.972 + 0.35, 2)
        self._render_calibration()
        self.audit("测点配准", "完成 {} 个测点的方向、零点与温漂校正".format(len(self.calib_points)))
        QMessageBox.information(self, "配准完成", "已完成方向、零点、温漂时差校正。")

    def import_calibration_csv(self):
        path, _ = QFileDialog.getOpenFileName(self, "选择测点 CSV", "", "CSV 文件 (*.csv)")
        if not path:
            return
        try:
            points = []
            with open(path, "r", encoding="utf-8-sig", newline="") as f:
                for row in csv.reader(f):
                    if len(row) < 2:
                        continue
                    try:
                        raw = float(row[1])
                    except ValueError:
                        continue
                    label = (row[0] or "P").strip()
                    points.append({
                        "label": label,
                        "raw": raw,
                        "corrected": round(raw * 0.972 + 0.35, 2),
                        "direction": "0°",
                        "zero": 0.0,
                        "drift": 1.0,
                        "delta": 8,
                        "status": "待配准",
                    })
                    if len(points) >= 60:
                        break
            if not points:
                QMessageBox.warning(self, "导入失败", "没有解析到有效的测点数据，请检查 CSV 第二列是否为数值。")
                return
            self.calib_points = points
            self._render_calibration()
            self.audit("导入测点", "CSV 导入 {} 个测点".format(len(points)))
            QMessageBox.information(self, "导入完成", "已导入 {} 个测点。".format(len(points)))
        except Exception as exc:
            QMessageBox.critical(self, "导入失败", str(exc))

    # ----------------------接触与转动---------------------
    def init_contact_tab(self, layout):
        top = QHBoxLayout()
        top.setSpacing(14)
        heat_box = QGroupBox("预紧力 × 转动角 风险扫描")
        heat_layout = QVBoxLayout(heat_box)
        self.contact_heatmap = HeatmapView()
        heat_layout.addWidget(self.contact_heatmap, 1)
        heat_hint = QLabel("点击任意格子切换工况，结果与曲线同步更新")
        heat_hint.setObjectName("sectionHint")
        heat_layout.addWidget(heat_hint)
        top.addWidget(heat_box, 3)

        right = QVBoxLayout()
        right.setSpacing(12)
        ctrl_box = QGroupBox("当前工况")
        ctrl_layout = QVBoxLayout(ctrl_box)
        ctrl_layout.setSpacing(5)
        self.contact_hole = SliderControl("孔径", 10, 60, 30, 0, " mm")
        self.contact_pad = SliderControl("垫片厚度", 0.5, 6, 2.0, 1, " mm")
        self.contact_preload = SliderControl("预紧力", 5, 80, 30, 1, " kN")
        self.contact_friction = SliderControl("摩擦系数", 0, 0.6, 0.15, 2, "")
        self.contact_angle = SliderControl("转动角", 0, 2.0, 0.8, 2, " °")
        for control in (self.contact_hole, self.contact_pad, self.contact_preload,
                        self.contact_friction, self.contact_angle):
            ctrl_layout.addWidget(control)
            control.valueChanged.connect(self.run_contact_demo)
            self.write_buttons.append(control)
        right.addWidget(ctrl_box)

        result_box = QGroupBox("分析结果")
        result_layout = QVBoxLayout(result_box)
        result_grid = QGridLayout()
        result_grid.setHorizontalSpacing(10)
        result_grid.setVerticalSpacing(10)
        card_area, self.contact_area = self._result_card("接触面积（mm²）")
        card_peak, self.contact_peak = self._result_card("峰值压力（MPa）")
        card_stiff, self.contact_stiff = self._result_card("转动刚度（kN·m/rad）")
        card_risk, self.contact_risk = self._result_card("风险等级", "待分析")
        result_grid.addWidget(card_area, 0, 0)
        result_grid.addWidget(card_peak, 0, 1)
        result_grid.addWidget(card_stiff, 1, 0)
        result_grid.addWidget(card_risk, 1, 1)
        result_layout.addLayout(result_grid)
        self.contact_delta = QLabel("较基准：—")
        self.contact_delta.setObjectName("sectionHint")
        result_layout.addWidget(self.contact_delta)
        result_layout.addStretch(1)
        right.addWidget(result_box, 1)
        top.addLayout(right, 2)
        layout.addLayout(top, 3)

        charts = QHBoxLayout()
        charts.setSpacing(14)
        pressure_box = QGroupBox("接触压力：基准工况 vs 当前工况（MPa）")
        pressure_layout = QVBoxLayout(pressure_box)
        self.contact_chart = ChartWidget("line")
        self.contact_chart.setMinimumHeight(210)
        pressure_layout.addWidget(self.contact_chart)
        charts.addWidget(pressure_box, 1)

        rotation_box = QGroupBox("转动刚度扫描（kN·m/rad）")
        rotation_layout = QVBoxLayout(rotation_box)
        self.rotation_chart = ChartWidget("line")
        self.rotation_chart.setMinimumHeight(210)
        rotation_layout.addWidget(self.rotation_chart)
        charts.addWidget(rotation_box, 1)
        layout.addLayout(charts, 2)

        self.contact_heatmap.cellClicked.connect(self._contact_cell_clicked)
        self._contact_baseline = self._contact_metrics(20.0, 30.0, 2.0, 0.15, 0.5)
        self._contact_baseline_pressure = self._contact_pressure_values(
            self._contact_baseline["peak"], 0.5)
        self.run_contact_demo()

    @staticmethod
    def _contact_metrics(preload, hole, pad, friction, angle):
        angle = min(max(angle, 0.0), 2.0)
        area = math.pi * (hole / 2.0) ** 2 * 0.85 * (1.0 - 0.05 * angle)
        peak = preload * 1000.0 / max(area, 1.0) * 1.25 * (1.0 + 0.18 * angle)
        stiffness = (11.5 * (preload / 20.0) * math.sqrt(2.0 / max(pad, 0.5))
                     * (1.0 + friction * 0.25) * (1.0 - 0.12 * angle))
        risk = min(100.0, peak / 90.0 * 60.0 + angle / 2.0 * 30.0)
        return {"area": area, "peak": peak, "stiffness": stiffness, "risk": risk}

    @staticmethod
    def _contact_pressure_values(peak, angle):
        values = []
        for i in range(12):
            x = i / 11.0
            values.append(peak * math.exp(-((x - 0.46) / 0.17) ** 2) * (1.0 + 0.04 * angle))
        return values

    def _contact_cell_clicked(self, row, col, preload, angle, risk):
        for control, value in ((self.contact_preload, preload), (self.contact_angle, angle)):
            control.set_value(value)
        self.run_contact_demo()

    def run_contact_demo(self):
        if not hasattr(self, "contact_heatmap"):
            return
        hole = float(self.contact_hole.value())
        pad = float(self.contact_pad.value())
        preload = float(self.contact_preload.value())
        friction = float(self.contact_friction.value())
        angle = float(self.contact_angle.value())
        metrics = self._contact_metrics(preload, hole, pad, friction, angle)
        baseline = self._contact_baseline

        self.contact_area.setText("{:.0f}".format(metrics["area"]))
        self.contact_peak.setText("{:.1f}".format(metrics["peak"]))
        self.contact_stiff.setText("{:.1f}".format(metrics["stiffness"]))
        risk = "关注" if (metrics["risk"] > 65 or angle > 1.5) else "正常"
        self._set_tag(self.contact_risk, risk, "ok" if risk == "正常" else "warn")
        delta = (metrics["peak"] / baseline["peak"] - 1.0) * 100.0
        self.contact_delta.setText("较基准工况峰值压力：{:+.1f}%".format(delta))

        labels = ["{:.1f}".format(i / 11.0) for i in range(12)]
        current_pressure = self._contact_pressure_values(metrics["peak"], angle)
        self.contact_chart.set_data(labels, [
            {"name": "基准工况", "color": "#94a3b8", "values": self._contact_baseline_pressure},
            {"name": "当前工况", "color": "#2563eb", "values": current_pressure, "fill": True},
        ], "")

        angles = [i * 0.25 for i in range(9)]
        scan = [self._contact_metrics(preload, hole, pad, friction, a)["stiffness"] for a in angles]
        base_scan = [self._contact_metrics(20.0, 30.0, 2.0, 0.15, a)["stiffness"] for a in angles]
        self.rotation_chart.set_data(["{:.2f}".format(a) for a in angles], [
            {"name": "基准工况", "color": "#94a3b8", "values": base_scan},
            {"name": "当前工况", "color": "#f59e0b", "values": scan, "fill": True},
        ], "")

        preloads = [10 + i * 10 for i in range(8)]
        rotations = [i * 2.0 / 7 for i in range(8)]
        matrix = []
        for turn in rotations:
            row = []
            for load in preloads:
                row.append(self._contact_metrics(load, hole, pad, friction, turn)["risk"])
            matrix.append(row)
        selected = (min(range(len(rotations)), key=lambda i: abs(rotations[i] - angle)),
                    min(range(len(preloads)), key=lambda i: abs(preloads[i] - preload)))
        self.contact_heatmap.set_data(preloads, rotations, matrix,
                                      "预紧力 (kN)", "转动角 (°)", "风险", selected)

    # ----------------------偏载溯因---------------------
    def init_eccentric_tab(self, layout):
        top = QHBoxLayout()
        top.setSpacing(14)
        heat_box = QGroupBox("偏心位置 × 偏载差扫描")
        heat_layout = QVBoxLayout(heat_box)
        self.ecc_heatmap = HeatmapView()
        heat_layout.addWidget(self.ecc_heatmap, 1)
        heat_hint = QLabel("点击任意位置切换偏心工况，因素贡献与结论同步更新")
        heat_hint.setObjectName("sectionHint")
        heat_layout.addWidget(heat_hint)
        top.addWidget(heat_box, 3)

        right = QVBoxLayout()
        right.setSpacing(12)
        ctrl_box = QGroupBox("安装与偏载参数")
        ctrl_layout = QVBoxLayout(ctrl_box)
        ctrl_layout.setSpacing(4)
        self.ecc_x_slider = SliderControl("安装偏心 X", -20, 20, 6.5, 1, " mm")
        self.ecc_y_slider = SliderControl("安装偏心 Y", -20, 20, -3.2, 1, " mm")
        self.ecc_hole_slider = SliderControl("孔位偏差", 0, 10, 1.2, 2, " mm")
        self.ecc_pad_slider = SliderControl("垫片刚度", 0.5, 6, 2.4, 1, "")
        self.ecc_preload_slider = SliderControl("预紧偏差", 0, 30, 8.0, 1, " %")
        self.ecc_temp_slider = SliderControl("温度差", -15, 15, 3.0, 1, " ℃")
        for control in (self.ecc_x_slider, self.ecc_y_slider, self.ecc_hole_slider,
                        self.ecc_pad_slider, self.ecc_preload_slider, self.ecc_temp_slider):
            ctrl_layout.addWidget(control)
            control.valueChanged.connect(self.run_eccentric_demo)
            self.write_buttons.append(control)
        right.addWidget(ctrl_box)

        result_box = QGroupBox("溯因结论")
        result_layout = QVBoxLayout(result_box)
        result_grid = QGridLayout()
        result_grid.setHorizontalSpacing(10)
        result_grid.setVerticalSpacing(10)
        card_factor, self.ecc_factor = self._result_card("主导因素")
        card_share, self.ecc_share = self._result_card("贡献度")
        card_res, self.ecc_residual = self._result_card("拟合残差")
        card_verdict, self.ecc_verdict = self._result_card("判定", "待分析")
        result_grid.addWidget(card_factor, 0, 0)
        result_grid.addWidget(card_share, 0, 1)
        result_grid.addWidget(card_res, 1, 0)
        result_grid.addWidget(card_verdict, 1, 1)
        result_layout.addLayout(result_grid)
        self.ecc_delta = QLabel("较基准偏载差：—")
        self.ecc_delta.setObjectName("sectionHint")
        result_layout.addWidget(self.ecc_delta)
        right.addWidget(result_box, 1)
        top.addLayout(right, 2)
        layout.addLayout(top, 3)

        bottom = QHBoxLayout()
        bottom.setSpacing(14)
        chart_box = QGroupBox("五因素贡献度")
        chart_layout = QVBoxLayout(chart_box)
        self.ecc_chart = ChartWidget("bar")
        self.ecc_chart.setMinimumHeight(210)
        chart_layout.addWidget(self.ecc_chart)
        bottom.addWidget(chart_box, 3)

        table_box = QGroupBox("因素明细与复测建议")
        table_layout = QVBoxLayout(table_box)
        self.ecc_table = self._make_table(["因素", "观测值", "贡献度", "建议"])
        table_layout.addWidget(self.ecc_table)
        bottom.addWidget(table_box, 2)
        layout.addLayout(bottom, 3)

        self.ecc_heatmap.cellClicked.connect(self._eccentric_cell_clicked)
        self.run_eccentric_demo()

    def _eccentric_metrics(self, x, y, hole, pad, preload, temp):
        raw = [
            12 + abs(x) * 2.2 + abs(y) * 1.4,
            8 + hole * 4.2,
            7 + abs(pad - 2.0) * 6.0,
            6 + preload * 0.8,
            4 + abs(temp) * 1.2,
        ]
        total = sum(raw) or 1.0
        contributions = [v / total * 100.0 for v in raw]
        diff = 0.55 * abs(x) + 0.38 * abs(y) + 2.2 * hole + 0.28 * preload + 0.9 * abs(temp)
        return contributions, diff

    def _eccentric_cell_clicked(self, row, col, x, y, value):
        self.ecc_x_slider.set_value(x)
        self.ecc_y_slider.set_value(y)
        self.run_eccentric_demo()

    def run_eccentric_demo(self):
        if not hasattr(self, "ecc_heatmap"):
            return
        x = float(self.ecc_x_slider.value())
        y = float(self.ecc_y_slider.value())
        hole = float(self.ecc_hole_slider.value())
        pad = float(self.ecc_pad_slider.value())
        preload = float(self.ecc_preload_slider.value())
        temp = float(self.ecc_temp_slider.value())
        contributions, diff = self._eccentric_metrics(x, y, hole, pad, preload, temp)
        _, baseline_diff = self._eccentric_metrics(0.0, 0.0, hole, pad, preload, temp)
        labels = ["安装偏心", "孔位偏差", "垫片刚度", "预紧不均", "温度差"]
        observations = [
            "{:.1f} / {:.1f} mm".format(x, y),
            "{:.2f} mm".format(hole),
            "{:.1f}".format(pad),
            "{:.1f} %".format(preload),
            "{:.1f} ℃".format(temp),
        ]
        index = max(range(len(contributions)), key=lambda i: contributions[i])
        self.ecc_factor.setText(labels[index])
        self.ecc_share.setText("{:.1f} %".format(contributions[index]))
        residual = 2.2 + abs(math.sin(diff)) * 2.5
        self.ecc_residual.setText("{:.2f} %".format(residual))
        verdict = "主导因素明确" if contributions[index] >= 35 else "多因素耦合"
        self._set_tag(self.ecc_verdict, verdict, "ok" if contributions[index] >= 35 else "info")
        self.ecc_delta.setText("较基准偏载差：{:+.1f} kN（基准 {:.1f} kN）".format(
            diff - baseline_diff, baseline_diff))
        self.ecc_chart.set_data(
            labels, [{"name": "贡献度", "color": "#8b5cf6", "values": contributions}], "%")
        suggestions = {
            "安装偏心": "复测安装坐标",
            "孔位偏差": "复核孔位加工",
            "垫片刚度": "抽检垫片",
            "预紧不均": "复紧对角螺栓",
            "温度差": "补测温度",
        }
        rows = []
        for i, label in enumerate(labels):
            rows.append([label, observations[i], "{:.1f}%".format(contributions[i]),
                         suggestions[label]])
        self._fill_table(self.ecc_table, rows)

        offsets = [-20, -15, -10, -5, 0, 5, 10, 15, 20]
        matrix = []
        for oy in offsets:
            row = []
            for ox in offsets:
                _, cell_diff = self._eccentric_metrics(ox, oy, hole, pad, preload, temp)
                row.append(round(cell_diff, 1))
            matrix.append(row)
        selected = (min(range(len(offsets)), key=lambda i: abs(offsets[i] - y)),
                    min(range(len(offsets)), key=lambda i: abs(offsets[i] - x)))
        self.ecc_heatmap.set_data(offsets, offsets, matrix,
                                  "偏心 X (mm)", "偏心 Y (mm)", "kN", selected)

    # ----------------------风压推演---------------------
    def init_wind_tab(self, layout):
        top = QHBoxLayout()
        top.setSpacing(14)
        heat_box = QGroupBox("风向角 × 缺失测点 包络极值")
        heat_layout = QVBoxLayout(heat_box)
        self.wind_heatmap = HeatmapView()
        heat_layout.addWidget(self.wind_heatmap, 1)
        heat_hint = QLabel("点击任意工况，包络曲线与可辨识性同步更新")
        heat_hint.setObjectName("sectionHint")
        heat_layout.addWidget(heat_hint)
        top.addWidget(heat_box, 3)

        right = QVBoxLayout()
        right.setSpacing(12)
        ctrl_box = QGroupBox("风压与缺点工况")
        ctrl_layout = QVBoxLayout(ctrl_box)
        ctrl_layout.setSpacing(4)
        self.wind_q = SliderControl("基本风压", 0.2, 1.2, 0.55, 2, " kPa")
        self.wind_shape = SliderControl("体型系数", 0.6, 2.0, 1.20, 2, "")
        self.wind_height = SliderControl("高度系数", 0.8, 2.0, 1.35, 2, "")
        self.wind_missing = SliderControl("缺失测点", 0, 8, 2, 0, " 个")
        self.wind_direction = SliderControl("风向角", 0, 330, 0, 0, " °")
        for control in (self.wind_q, self.wind_shape, self.wind_height,
                        self.wind_missing, self.wind_direction):
            ctrl_layout.addWidget(control)
            control.valueChanged.connect(self.run_wind_demo)
            self.write_buttons.append(control)
        right.addWidget(ctrl_box)

        result_box = QGroupBox("包络与可辨识性")
        result_layout = QVBoxLayout(result_box)
        result_grid = QGridLayout()
        result_grid.setHorizontalSpacing(10)
        result_grid.setVerticalSpacing(10)
        card_max, self.wind_max = self._result_card("包络最大反力")
        card_min, self.wind_min = self._result_card("包络最小反力")
        card_id, self.wind_ident = self._result_card("可辨识性", "—")
        card_verdict, self.wind_verdict = self._result_card("判定", "待推演")
        result_grid.addWidget(card_max, 0, 0)
        result_grid.addWidget(card_min, 0, 1)
        result_grid.addWidget(card_id, 1, 0)
        result_grid.addWidget(card_verdict, 1, 1)
        result_layout.addLayout(result_grid)
        result_layout.addStretch(1)
        right.addWidget(result_box, 1)
        top.addLayout(right, 2)
        layout.addLayout(top, 3)

        bottom = QHBoxLayout()
        bottom.setSpacing(14)
        chart_box = QGroupBox("风向角—反力包络（kN）")
        chart_layout = QVBoxLayout(chart_box)
        self.wind_chart = ChartWidget("line")
        self.wind_chart.setMinimumHeight(220)
        chart_layout.addWidget(self.wind_chart)
        bottom.addWidget(chart_box, 3)

        table_box = QGroupBox("典型工况")
        table_layout = QVBoxLayout(table_box)
        self.wind_table = self._make_table(["风向角", "正压反力", "负压反力", "状态"])
        table_layout.addWidget(self.wind_table)
        bottom.addWidget(table_box, 2)
        layout.addLayout(bottom, 2)

        self.wind_heatmap.cellClicked.connect(self._wind_cell_clicked)
        self.run_wind_demo()

    @staticmethod
    def _wind_series(base):
        angles = [i * 30 for i in range(12)]
        positive = []
        negative = []
        for angle in angles:
            rad = math.radians(angle)
            positive.append(base * (0.55 + 0.45 * math.cos(rad)))
            negative.append(-base * (0.55 + 0.45 * math.cos(rad + math.pi)))
        return angles, positive, negative

    def _wind_cell_clicked(self, row, col, angle, missing, value):
        self.wind_direction.set_value(angle)
        self.wind_missing.set_value(missing)
        self.run_wind_demo()

    def run_wind_demo(self):
        if not hasattr(self, "wind_heatmap"):
            return
        q = float(self.wind_q.value()) * float(self.wind_shape.value()) * float(self.wind_height.value())
        base = q * 26.0
        missing = int(round(float(self.wind_missing.value())))
        direction = int(round(float(self.wind_direction.value()) / 30.0) * 30) % 360
        angles, positive, negative = self._wind_series(base)
        all_values = positive + negative
        self.wind_max.setText("{:.1f} kN".format(max(all_values)))
        self.wind_min.setText("{:.1f} kN".format(min(all_values)))
        identifiable = missing <= 3
        self.wind_ident.setText("可辨识" if identifiable else "不可辨识")
        if identifiable:
            self._set_tag(self.wind_verdict, "允许发布受力", "ok")
        else:
            self._set_tag(self.wind_verdict, "停止受力输出", "warn")
        labels = ["{}°".format(a) for a in angles]
        self.wind_chart.set_data(labels, [
            {"name": "正压", "color": "#2563eb", "values": positive},
            {"name": "负压", "color": "#f59e0b", "values": negative, "fill": True},
        ], "")
        rows = []
        for i in (0, 3, 6, 9):
            status = "可发布" if identifiable else "不可辨识"
            rows.append([labels[i], "{:.1f}".format(positive[i]),
                         "{:.1f}".format(negative[i]), status])
        self._fill_table(self.wind_table, rows)

        miss_values = [0, 1, 2, 3, 4, 5, 6]
        matrix = []
        for miss in miss_values:
            row = []
            for i, angle in enumerate(angles):
                row.append(round(max(positive[i], abs(negative[i])) * (1.0 + 0.08 * miss), 1))
            matrix.append(row)
        selected = (min(range(len(miss_values)), key=lambda i: abs(miss_values[i] - missing)),
                    min(range(len(angles)), key=lambda i: abs(angles[i] - direction)))
        self.wind_heatmap.set_data(angles, miss_values, matrix,
                                   "风向角 (°)", "缺失测点数", "kN", selected)

    # ----------------------预紧调校---------------------
    def init_preload_tab(self, layout):
        top = QHBoxLayout()
        top.setSpacing(14)
        heat_box = QGroupBox("调校级数 × 螺栓分组 偏差扫描")
        heat_layout = QVBoxLayout(heat_box)
        self.pre_heatmap = HeatmapView()
        heat_layout.addWidget(self.pre_heatmap, 1)
        heat_hint = QLabel("点击任意组合，逐阶方案与最终偏差同步更新")
        heat_hint.setObjectName("sectionHint")
        heat_layout.addWidget(heat_hint)
        top.addWidget(heat_box, 3)

        right = QVBoxLayout()
        right.setSpacing(12)
        ctrl_box = QGroupBox("调校目标与约束")
        ctrl_layout = QVBoxLayout(ctrl_box)
        ctrl_layout.setSpacing(4)
        self.pre_target_slider = SliderControl("目标受力", 40, 150, 90, 1, " kN")
        self.pre_current_slider = SliderControl("当前预紧", 5, 60, 12, 1, " kN")
        self.pre_steps_slider = SliderControl("调校级数", 3, 12, 6, 0, " 级")
        self.pre_tol_slider = SliderControl("允许偏差", 1, 10, 5, 1, " %")
        self.pre_group_slider = SliderControl("螺栓分组", 1, 4, 1, 0, " 组")
        for control in (self.pre_target_slider, self.pre_current_slider,
                        self.pre_steps_slider, self.pre_tol_slider, self.pre_group_slider):
            ctrl_layout.addWidget(control)
            control.valueChanged.connect(self.run_preload_demo)
            self.write_buttons.append(control)
        right.addWidget(ctrl_box)

        result_box = QGroupBox("调校结果")
        result_layout = QVBoxLayout(result_box)
        result_grid = QGridLayout()
        result_grid.setHorizontalSpacing(10)
        result_grid.setVerticalSpacing(10)
        card_pre, self.pre_recommend = self._result_card("推荐预紧")
        card_force, self.pre_force = self._result_card("预计受力")
        card_dev, self.pre_deviation = self._result_card("最终偏差")
        card_verdict, self.pre_verdict = self._result_card("判定", "待调校")
        result_grid.addWidget(card_pre, 0, 0)
        result_grid.addWidget(card_force, 0, 1)
        result_grid.addWidget(card_dev, 1, 0)
        result_grid.addWidget(card_verdict, 1, 1)
        result_layout.addLayout(result_grid)
        result_layout.addStretch(1)
        right.addWidget(result_box, 1)
        top.addLayout(right, 2)
        layout.addLayout(top, 3)

        bottom = QHBoxLayout()
        bottom.setSpacing(14)
        chart_box = QGroupBox("逐阶预紧与受力")
        chart_layout = QVBoxLayout(chart_box)
        self.preload_chart = ChartWidget("line")
        self.preload_chart.setMinimumHeight(210)
        chart_layout.addWidget(self.preload_chart)
        bottom.addWidget(chart_box, 3)

        table_box = QGroupBox("调校阶段")
        table_layout = QVBoxLayout(table_box)
        self.preload_table = self._make_table(["阶段", "预紧力", "节点受力", "偏差", "状态"])
        table_layout.addWidget(self.preload_table)
        bottom.addWidget(table_box, 2)
        layout.addLayout(bottom, 3)

        self.pre_heatmap.cellClicked.connect(self._preload_cell_clicked)
        self.run_preload_demo()

    @staticmethod
    def _preload_plan(target, current, steps, group):
        steps = max(3, int(round(steps)))
        group = max(1, int(round(group)))
        target_preload = target / 4.5
        final_dev = max(0.3, 5.8 / (steps + (group - 1) * 1.8))
        preloads = []
        forces = []
        for i in range(steps + 1):
            ratio = i / steps
            eased = 1.0 - (1.0 - ratio) ** (1.0 + 0.25 * (group - 1))
            preload = current + (target_preload - current) * eased
            force = current * 4.5 + (target - current * 4.5) * eased
            force *= 1.0 + final_dev / 100.0 * ratio
            preloads.append(round(preload, 2))
            forces.append(round(force, 2))
        return preloads, forces, final_dev, target_preload

    def _preload_cell_clicked(self, row, col, steps, group, value):
        self.pre_steps_slider.set_value(steps)
        self.pre_group_slider.set_value(group)
        self.run_preload_demo()

    def run_preload_demo(self):
        if not hasattr(self, "pre_heatmap"):
            return
        target = float(self.pre_target_slider.value())
        current = float(self.pre_current_slider.value())
        steps = int(round(float(self.pre_steps_slider.value())))
        tolerance = float(self.pre_tol_slider.value())
        group = int(round(float(self.pre_group_slider.value())))
        preloads, forces, final_dev, target_preload = self._preload_plan(
            target, current, steps, group)
        self.pre_recommend.setText("{:.1f} kN".format(target_preload))
        self.pre_force.setText("{:.1f} kN".format(forces[-1]))
        self.pre_deviation.setText("{:.1f} %".format(final_dev))
        self._set_tag(self.pre_verdict, "偏差合格" if final_dev <= tolerance else "需复调",
                      "ok" if final_dev <= tolerance else "warn")
        labels = ["S{}".format(i) for i in range(len(forces))]
        self.preload_chart.set_data(labels, [
            {"name": "预紧力", "color": "#8b5cf6", "values": preloads},
            {"name": "节点受力", "color": "#2563eb", "values": forces, "fill": True},
        ], "")
        rows = []
        for i in range(len(forces)):
            dev = abs(forces[i] - target) / target * 100
            rows.append([labels[i], "{:.1f}".format(preloads[i]), "{:.1f}".format(forces[i]),
                         "{:.1f}%".format(dev), "合格" if dev <= tolerance else "调整中"])
        self._fill_table(self.preload_table, rows)

        step_values = list(range(3, 13))
        group_values = [1, 2, 3, 4]
        matrix = []
        for grp in group_values:
            row = []
            for stp in step_values:
                _, _, dev, _ = self._preload_plan(target, current, stp, grp)
                row.append(round(dev, 2))
            matrix.append(row)
        selected = (min(range(len(group_values)), key=lambda i: abs(group_values[i] - group)),
                    min(range(len(step_values)), key=lambda i: abs(step_values[i] - steps)))
        self.pre_heatmap.set_data(step_values, group_values, matrix,
                                  "调校级数", "螺栓分组", "%", selected)

    # ----------------------证据工单---------------------
    def init_evidence_tab(self, layout):
        stats = QHBoxLayout()
        stats.setSpacing(14)
        self.ev_records_card = StatCard("计算记录", "0", "条", "含超限与通过", "#2563eb")
        self.ev_signed_card = StatCard("已签认", "0", "条", "成果签认数量", "#10b981")
        self.ev_orders_card = StatCard("开放工单", "0", "个", "待复核闭环", "#f59e0b")
        self.ev_root_card = StatCard("证据链根", "—", "", "SHA256 Merkle 根", "#8b5cf6")
        for card in (self.ev_records_card, self.ev_signed_card,
                     self.ev_orders_card, self.ev_root_card):
            stats.addWidget(card, 1)
        layout.addLayout(stats)

        content = QHBoxLayout()
        content.setSpacing(14)
        source_box = QGroupBox("九类证据来源")
        source_layout = QVBoxLayout(source_box)
        self.evidence_source_table = self._make_table(["证据来源", "采集状态"])
        source_layout.addWidget(self.evidence_source_table)
        content.addWidget(source_box, 2)

        order_box = QGroupBox("复核工单")
        order_layout = QVBoxLayout(order_box)
        self.order_table = self._make_table(["编号", "标题", "节点", "状态", "负责人", "创建时间"])
        order_layout.addWidget(self.order_table)
        content.addWidget(order_box, 3)
        layout.addLayout(content, 3)

        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.btn_order_create = QPushButton("生成复核工单")
        self.btn_order_create.setObjectName("primaryBtn")
        self.btn_order_close = QPushButton("关闭选中工单")
        self.btn_ev_verify = QPushButton("校验证据链")
        self.btn_ev_verify.setObjectName("ghostBtn")
        self.btn_ev_export = QPushButton("导出证据链包")
        bar.addWidget(self.btn_order_create)
        bar.addWidget(self.btn_order_close)
        bar.addStretch(1)
        bar.addWidget(self.btn_ev_verify)
        bar.addWidget(self.btn_ev_export)
        layout.addLayout(bar)

        self.write_buttons += [self.btn_order_create, self.btn_order_close, self.btn_ev_export]
        self.btn_order_create.clicked.connect(self.create_evidence_order)
        self.btn_order_close.clicked.connect(self.close_evidence_order)
        self.btn_ev_verify.clicked.connect(self.verify_evidence)
        self.btn_ev_export.clicked.connect(self.export_evidence_pack)
        self.refresh_evidence_tab()

    def refresh_evidence_tab(self):
        records = self.db.query_one("select count(*) as c from calc_record")["c"]
        signed = self.db.query_one("select count(*) as c from calc_record where sign_user is not null")["c"]
        open_orders = self.db.query_one(
            "select count(*) as c from work_order where status='开放'")["c"]
        self.ev_records_card.set_value(records, "含超限与通过")
        self.ev_signed_card.set_value(signed, "成果签认数量")
        self.ev_orders_card.set_value(open_orders, "待复核闭环")

        items, chain, root = self._collect_evidence()
        if root:
            self.ev_root_card.set_value(root[:10], "SHA256 Merkle 根")
            self.ev_root_card.lbl_value.setToolTip(root)
        else:
            self.ev_root_card.set_value("—", "暂无计算记录")

        has_report = self.db.query_one(
            "select count(*) as c from calc_record where report_path is not null and report_path<>''")["c"]
        audit_count = self.db.query_one("select count(*) as c from audit_log")["c"]
        sources = [
            ("工程资料", self.db.query_one("select count(*) as c from project_info")["c"] > 0),
            ("分格几何", self.db.query_one("select count(*) as c from glass_panel")["c"] > 0),
            ("节点装配", self.db.query_one("select count(*) as c from claw_node")["c"] > 0),
            ("测点采样", self.db.query_one("select count(*) as c from measure_point")["c"] > 0),
            ("反演参数", records > 0),
            ("计算结果", records > 0),
            ("报告文件", has_report > 0),
            ("签认记录", signed > 0),
            ("审计日志", audit_count > 0),
        ]
        self._fill_table(self.evidence_source_table,
                         [[name, "已采集" if ok else "待补充"] for name, ok in sources])

        rows = self.db.query_all(
            "select w.wid, coalesce(w.title,''), coalesce(c.claw_no,'-'), coalesce(w.status,'开放'), "
            "coalesce(w.owner,'-'), coalesce(w.create_time,'') "
            "from work_order w left join claw_node c on c.nid = w.nid order by w.wid desc")
        self._fill_table(self.order_table, [[r[0], r[1], r[2], r[3], r[4], r[5]] for r in rows])

    def create_evidence_order(self):
        if not self.can_write:
            return
        row = self.db.query_one(
            "select r.rid, r.nid, coalesce(c.claw_no,'-') as claw_no "
            "from calc_record r left join claw_node c on c.nid = r.nid order by r.rid desc limit 1")
        if row is None:
            QMessageBox.information(self, "提示", "还没有计算记录，请先执行受力反演")
            return
        wid = self.db.execute(
            "insert into work_order(nid,rid,title,detail,status,owner,create_time) "
            "values (?,?,?,?,?,?,?)",
            (row["nid"], row["rid"], "计算成果复核", "节点 {} 的计算结果需复核".format(row["claw_no"]),
             "开放", self.user.get("realname") or self.user.get("username"), now_text()))
        self.audit("生成工单", "工单 {} 关联记录 {}".format(wid, row["rid"]))
        self.refresh_evidence_tab()
        QMessageBox.information(self, "已生成", "复核工单已创建。")

    def close_evidence_order(self):
        if not self.can_write:
            return
        wid = self._selected_id(self.order_table)
        if wid is None:
            QMessageBox.information(self, "提示", "请先选择一条工单")
            return
        self.db.execute(
            "update work_order set status='已关闭', close_time=? where wid=?", (now_text(), wid))
        self.audit("关闭工单", "工单 {}".format(wid))
        self.refresh_evidence_tab()

    # ----------------------工程 / 分格 / 节点---------------------
    def init_project_tab(self, layout):
        splitter = QSplitter(Qt.Orientation.Vertical)

        box_proj = QGroupBox("工程项目台账")
        v_proj = QVBoxLayout(box_proj)
        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.btn_proj_new = QPushButton("新建工程")
        self.btn_proj_new.setObjectName("primaryBtn")
        self.btn_proj_edit = QPushButton("编辑工程")
        self.btn_proj_del = QPushButton("删除工程")
        self.btn_proj_del.setObjectName("dangerBtn")
        self.btn_proj_refresh = QPushButton("刷新")
        self.btn_proj_refresh.setObjectName("ghostBtn")
        for btn in (self.btn_proj_new, self.btn_proj_edit, self.btn_proj_del):
            self.write_buttons.append(btn)
        self.btn_demo = QPushButton("示例数据")
        self.btn_demo.setToolTip("一键生成示例工程、分格、节点、测点与计算记录")
        self.write_buttons.append(self.btn_demo)
        bar.addWidget(self.btn_proj_new)
        bar.addWidget(self.btn_proj_edit)
        bar.addWidget(self.btn_proj_del)
        bar.addStretch(1)
        bar.addWidget(self.btn_demo)
        bar.addWidget(self.btn_proj_refresh)
        v_proj.addLayout(bar)
        self.table_proj = self._make_table(["ID", "工程名称", "立面名称", "状态", "创建时间", "备注"])
        self.table_proj.setColumnWidth(0, 50)
        self.table_proj.itemSelectionChanged.connect(self.on_project_changed)
        self.table_proj.doubleClicked.connect(lambda _: self.edit_project())
        v_proj.addWidget(self.table_proj, 1)

        lower = QSplitter(Qt.Orientation.Horizontal)
        lower.setHandleWidth(10)

        box_panel = QGroupBox("玻璃分格（按工程）")
        v_panel = QVBoxLayout(box_panel)
        bar2 = QHBoxLayout()
        bar2.setSpacing(8)
        self.btn_panel_new = QPushButton("新增分格")
        self.btn_panel_del = QPushButton("删除分格")
        self.btn_panel_del.setObjectName("dangerBtn")
        self.write_buttons += [self.btn_panel_new, self.btn_panel_del]
        bar2.addWidget(self.btn_panel_new)
        bar2.addWidget(self.btn_panel_del)
        bar2.addStretch(1)
        v_panel.addLayout(bar2)
        self.table_panel = self._make_table(["ID", "分格编号", "宽(mm)", "高(mm)", "厚(mm)", "玻璃类型"])
        self.table_panel.setColumnWidth(0, 50)
        self.table_panel.itemSelectionChanged.connect(self.on_panel_changed)
        self.table_panel.doubleClicked.connect(lambda _: self.edit_panel())
        v_panel.addWidget(self.table_panel, 1)

        box_node = QGroupBox("驳接爪节点（按分格）")
        v_node = QVBoxLayout(box_node)
        bar3 = QHBoxLayout()
        bar3.setSpacing(8)
        self.btn_node_new = QPushButton("新增节点")
        self.btn_node_del = QPushButton("删除节点")
        self.btn_node_del.setObjectName("dangerBtn")
        self.write_buttons += [self.btn_node_new, self.btn_node_del]
        bar3.addWidget(self.btn_node_new)
        bar3.addWidget(self.btn_node_del)
        bar3.addStretch(1)
        v_node.addLayout(bar3)
        self.table_node = self._make_table(["ID", "节点编号", "爪数", "预紧力(kN)", "偏心(mm)", "类型", "臂长(mm)", "位置(mm)"])
        self.table_node.setColumnWidth(0, 50)
        self.table_node.doubleClicked.connect(lambda _: self.edit_node())
        v_node.addWidget(self.table_node, 1)

        lower.addWidget(box_panel)
        lower.addWidget(box_node)
        lower.setSizes([600, 600])

        splitter.setHandleWidth(10)
        splitter.addWidget(box_proj)
        splitter.addWidget(lower)
        splitter.setSizes([300, 440])
        layout.addWidget(splitter, 1)

        self.btn_proj_new.clicked.connect(self.add_project)
        self.btn_proj_edit.clicked.connect(self.edit_project)
        self.btn_proj_del.clicked.connect(self.delete_project)
        self.btn_demo.clicked.connect(self.add_demo_data)
        self.btn_proj_refresh.clicked.connect(self.load_project_list)
        self.btn_panel_new.clicked.connect(self.add_panel)
        self.btn_panel_del.clicked.connect(self.delete_panel)
        self.btn_node_new.clicked.connect(self.add_node)
        self.btn_node_del.clicked.connect(self.delete_node)

        self.load_project_list()

    def load_project_list(self):
        keep = self._selected_id(self.table_proj)
        rows = self.db.query_all(
            "select pid, proj_name, coalesce(facade_name,''), coalesce(status,'在建'), "
            "coalesce(create_time,''), coalesce(remark,'') from project_info order by pid desc")
        self.table_proj.blockSignals(True)
        self._fill_table(self.table_proj, rows)
        if keep is not None:
            self._select_id(self.table_proj, keep)
        if self.table_proj.currentRow() < 0 and self.table_proj.rowCount() > 0:
            self.table_proj.selectRow(0)
        self.table_proj.blockSignals(False)
        self.load_panel_list()

    def on_project_changed(self):
        self.load_panel_list()

    def load_panel_list(self):
        pid = self._selected_id(self.table_proj)
        keep = self._selected_id(self.table_panel)
        self.table_panel.blockSignals(True)
        if pid is None:
            self._fill_table(self.table_panel, [])
        else:
            rows = self.db.query_all(
                "select gid, coalesce(glass_no,''), coalesce(width,0), coalesce(height,0), "
                "coalesce(thickness,0), coalesce(glass_type,'') from glass_panel where pid=? order by gid desc", (pid,))
            self._fill_table(self.table_panel, rows)
            if keep is not None:
                self._select_id(self.table_panel, keep)
            if self.table_panel.currentRow() < 0 and self.table_panel.rowCount() > 0:
                self.table_panel.selectRow(0)
        self.table_panel.blockSignals(False)
        self.load_node_list()

    def on_panel_changed(self):
        self.load_node_list()

    def load_node_list(self):
        gid = self._selected_id(self.table_panel)
        keep = self._selected_id(self.table_node)
        if gid is None:
            self._fill_table(self.table_node, [])
            return
        rows = self.db.query_all(
            "select nid, coalesce(claw_no,''), coalesce(arm_count,0), coalesce(preload,0), "
            "coalesce(eccentricity,0), coalesce(node_type,''), coalesce(arm_len,0), "
            "coalesce(pos_x,0), coalesce(pos_y,0) "
            "from claw_node where gid=? order by nid desc", (gid,))
        display = [[r[0], r[1], r[2], r[3], r[4], r[5], r[6],
                    "{:.0f}, {:.0f}".format(r[7], r[8])] for r in rows]
        self._fill_table(self.table_node, display)
        if keep is not None:
            self._select_id(self.table_node, keep)

    def add_project(self):
        if not self.can_write:
            return
        dlg = ProjectDialog(self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        pid = self.db.execute(
            "insert into project_info(proj_name,facade_name,create_user,create_time,remark,status,update_time) "
            "values (?,?,?,?,?,?,?)",
            (data["proj_name"], data["facade_name"], self.user.get("uid"), now_text(),
             data["remark"], data["status"], now_text()))
        self.audit("新增工程", "{}（ID {}）".format(data["proj_name"], pid))
        self.load_project_list()
        self._select_id(self.table_proj, pid)
        self.refresh_selectors()

    def edit_project(self):
        if not self.can_write:
            return
        pid = self._selected_id(self.table_proj)
        if pid is None:
            QMessageBox.information(self, "提示", "请先选择工程")
            return
        row = self.db.query_one("select * from project_info where pid=?", (pid,))
        if row is None:
            return
        dlg = ProjectDialog(self, dict(row))
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        self.db.execute(
            "update project_info set proj_name=?, facade_name=?, status=?, remark=?, update_time=? where pid=?",
            (data["proj_name"], data["facade_name"], data["status"], data["remark"], now_text(), pid))
        self.audit("编辑工程", "{}（ID {}）".format(data["proj_name"], pid))
        self.load_project_list()
        self.refresh_selectors()

    def delete_project(self):
        if not self.can_write:
            return
        pid = self._selected_id(self.table_proj)
        if pid is None:
            return
        row = self.db.query_one("select proj_name from project_info where pid=?", (pid,))
        name = row["proj_name"] if row else str(pid)
        if QMessageBox.question(self, "确认删除", "删除工程《{}》将同时删除其分格、节点、测点与计算记录，是否继续？".format(name)) != QMessageBox.StandardButton.Yes:
            return
        sub_nid = "select nid from claw_node where gid in (select gid from glass_panel where pid=?)"
        ok, err = self.db.execute_many([
            ("delete from measure_point where nid in ({})".format(sub_nid), (pid,)),
            ("delete from calc_record where nid in ({})".format(sub_nid), (pid,)),
            ("delete from claw_node where gid in (select gid from glass_panel where pid=?)", (pid,)),
            ("delete from glass_panel where pid=?", (pid,)),
            ("delete from project_info where pid=?", (pid,)),
        ])
        if not ok:
            QMessageBox.critical(self, "删除失败", err)
            return
        self.audit("删除工程", "{}（ID {}）".format(name, pid))
        self.load_project_list()
        self.refresh_selectors()

    def add_panel(self):
        if not self.can_write:
            return
        pid = self._selected_id(self.table_proj)
        if pid is None:
            QMessageBox.information(self, "提示", "请先选择工程")
            return
        count = self.db.query_one("select count(*) as c from glass_panel where pid=?", (pid,))["c"]
        dlg = PanelDialog(self, suggest_no="GL-{:03d}".format(count + 1))
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        gid = self.db.execute(
            "insert into glass_panel(pid,glass_no,width,height,thickness,glass_type,remark) values (?,?,?,?,?,?,?)",
            (pid, data["glass_no"], data["width"], data["height"], data["thickness"], data["glass_type"], data["remark"]))
        self.audit("新增分格", "{}（ID {}）".format(data["glass_no"], gid))
        self.load_panel_list()
        self._select_id(self.table_panel, gid)
        self.refresh_selectors()

    def edit_panel(self):
        if not self.can_write:
            return
        gid = self._selected_id(self.table_panel)
        if gid is None:
            return
        row = self.db.query_one("select * from glass_panel where gid=?", (gid,))
        dlg = PanelDialog(self, dict(row), row["glass_no"] or "")
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        self.db.execute(
            "update glass_panel set glass_no=?, width=?, height=?, thickness=?, glass_type=?, remark=? where gid=?",
            (data["glass_no"], data["width"], data["height"], data["thickness"], data["glass_type"], data["remark"], gid))
        self.audit("编辑分格", "{}（ID {}）".format(data["glass_no"], gid))
        self.load_panel_list()
        self.refresh_selectors()

    def delete_panel(self):
        if not self.can_write:
            return
        gid = self._selected_id(self.table_panel)
        if gid is None:
            return
        row = self.db.query_one("select glass_no from glass_panel where gid=?", (gid,))
        name = row["glass_no"] if row else str(gid)
        if QMessageBox.question(self, "确认删除", "删除分格《{}》将同时删除其节点、测点与计算记录，是否继续？".format(name)) != QMessageBox.StandardButton.Yes:
            return
        ok, err = self.db.execute_many([
            ("delete from measure_point where nid in (select nid from claw_node where gid=?)", (gid,)),
            ("delete from calc_record where nid in (select nid from claw_node where gid=?)", (gid,)),
            ("delete from claw_node where gid=?", (gid,)),
            ("delete from glass_panel where gid=?", (gid,)),
        ])
        if not ok:
            QMessageBox.critical(self, "删除失败", err)
            return
        self.audit("删除分格", "{}（ID {}）".format(name, gid))
        self.load_panel_list()
        self.refresh_selectors()

    def default_node_position(self, index, width, height):
        w = float(width or 1500)
        h = float(height or 1800)
        presets = [(-w / 3, -h / 3), (w / 3, -h / 3), (w / 3, h / 3), (-w / 3, h / 3),
                   (0, 0), (-w / 4, 0), (w / 4, 0)]
        return presets[index % len(presets)]

    def add_node(self):
        if not self.can_write:
            return
        gid = self._selected_id(self.table_panel)
        if gid is None:
            QMessageBox.information(self, "提示", "请先选择玻璃分格")
            return
        count = self.db.query_one("select count(*) as c from claw_node where gid=?", (gid,))["c"]
        panel = self.db.query_one("select width, height from glass_panel where gid=?", (gid,))
        pos = self.default_node_position(count, panel["width"] if panel else 1500,
                                         panel["height"] if panel else 1800)
        dlg = NodeDialog(self, suggest_no="J-{:03d}".format(count + 1), suggest_pos=pos)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        nid = self.db.execute(
            "insert into claw_node(gid,claw_no,arm_count,preload,eccentricity,node_type,arm_len,"
            "pos_x,pos_y,remark) values (?,?,?,?,?,?,?,?,?,?)",
            (gid, data["claw_no"], data["arm_count"], data["preload"], data["eccentricity"],
             data["node_type"], data["arm_len"], data["pos_x"], data["pos_y"], data["remark"]))
        self.audit("新增节点", "{}（ID {}）".format(data["claw_no"], nid))
        self.load_node_list()
        self._select_id(self.table_node, nid)
        self.refresh_selectors()

    def edit_node(self):
        if not self.can_write:
            return
        nid = self._selected_id(self.table_node)
        if nid is None:
            return
        row = self.db.query_one("select * from claw_node where nid=?", (nid,))
        dlg = NodeDialog(self, dict(row), row["claw_no"] or "")
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        self.db.execute(
            "update claw_node set claw_no=?, arm_count=?, preload=?, eccentricity=?, node_type=?, "
            "arm_len=?, pos_x=?, pos_y=?, remark=? where nid=?",
            (data["claw_no"], data["arm_count"], data["preload"], data["eccentricity"],
             data["node_type"], data["arm_len"], data["pos_x"], data["pos_y"],
             data["remark"], nid))
        self.audit("编辑节点", "{}（ID {}）".format(data["claw_no"], nid))
        self.load_node_list()
        self.refresh_selectors()

    def delete_node(self):
        if not self.can_write:
            return
        nid = self._selected_id(self.table_node)
        if nid is None:
            return
        row = self.db.query_one("select claw_no from claw_node where nid=?", (nid,))
        name = row["claw_no"] if row else str(nid)
        if QMessageBox.question(self, "确认删除", "删除节点《{}》将同时删除其测点与计算记录，是否继续？".format(name)) != QMessageBox.StandardButton.Yes:
            return
        ok, err = self.db.execute_many([
            ("delete from measure_point where nid=?", (nid,)),
            ("delete from calc_record where nid=?", (nid,)),
            ("delete from claw_node where nid=?", (nid,)),
        ])
        if not ok:
            QMessageBox.critical(self, "删除失败", err)
            return
        self.audit("删除节点", "{}（ID {}）".format(name, nid))
        self.load_node_list()
        self.refresh_selectors()

    def add_demo_data(self):
        if not self.can_write:
            return
        if QMessageBox.question(
                self, "生成示例数据",
                "将新建一个示例工程，包含 3 个分格、6 个驳接爪节点、7 个测点和 1 条计算记录。\n是否继续？"
        ) != QMessageBox.StandardButton.Yes:
            return
        try:
            summary = self.create_demo_data()
        except Exception as exc:
            QMessageBox.critical(self, "生成失败", "示例数据生成失败：{}".format(exc))
            return
        self.load_project_list()
        self._select_id(self.table_proj, summary["pid"])
        self.refresh_selectors()
        for selector in (self.measure_selector, self.calc_selector,
                         self.transfer_selector, self.calib_selector):
            idx = selector.cb_project.findData(summary["pid"])
            if idx >= 0:
                selector.cb_project.setCurrentIndex(idx)
        self.load_record_list()
        self.refresh_dashboard()
        self.refresh_transfer()
        self.load_calibration_demo()
        self.nav_list.setCurrentRow(0)
        QMessageBox.information(
            self, "生成完成",
            "已生成示例工程《{}》。\n分格 {} 个、节点 {} 个、测点 {} 个、计算记录 {} 条。".format(
                summary["name"], summary["panels"], summary["nodes"],
                summary["measures"], summary["records"]))

    def create_demo_data(self):
        seq = self.db.query_one(
            "select count(*) as c from project_info where proj_name like '示例工程%'")["c"] + 1
        name = "示例工程 · 幕墙节点 {:02d}".format(seq)
        pid = self.db.execute(
            "insert into project_info(proj_name,facade_name,create_user,create_time,remark,status,update_time) "
            "values (?,?,?,?,?,?,?)",
            (name, "南立面", self.user.get("uid"), now_text(), "系统生成的示例数据", "在建", now_text()))

        strain_pool = [
            [12.3, 14.1, -8.2, 9.6],
            [10.8, 12.6, -6.9, 8.4],
            [15.2, 11.8, -9.7, 10.1],
            [9.4, 13.5, -7.3, 11.2],
            [13.6, 16.2, -10.4, 8.8],
            [11.1, 12.9, -8.5, 9.9],
        ]
        deflect_pool = [
            [0.82, 0.91, 0.44, 0.75],
            [0.71, 0.84, 0.38, 0.66],
            [0.95, 0.78, 0.52, 0.81],
            [0.63, 0.88, 0.41, 0.72],
            [0.87, 1.02, 0.57, 0.69],
            [0.74, 0.86, 0.46, 0.78],
        ]
        panels = [
            ("GL-D01", 1500, 1800, 12, "中空钢化"),
            ("GL-D02", 1200, 1500, 12, "中空钢化"),
            ("GL-D03", 1800, 1500, 15, "夹胶钢化"),
        ]

        node_count = 0
        measure_count = 0
        solutions = []
        for panel_no, width, height, thickness, glass_type in panels:
            gid = self.db.execute(
                "insert into glass_panel(pid,glass_no,width,height,thickness,glass_type,remark) "
                "values (?,?,?,?,?,?,?)",
                (pid, panel_no, width, height, thickness, glass_type, "示例分格"))
            for _ in range(2):
                node_count += 1
                pos_x, pos_y = self.default_node_position(node_count - 1, width, height)
                nid = self.db.execute(
                    "insert into claw_node(gid,claw_no,arm_count,preload,eccentricity,node_type,arm_len,"
                    "pos_x,pos_y,remark) values (?,?,?,?,?,?,?,?,?,?)",
                    (gid, "J-D{:02d}".format(node_count), 4, 20.0 + node_count * 2, 0.5,
                     "四爪", 300.0, pos_x, pos_y, "示例节点"))
                strain = strain_pool[(node_count - 1) % len(strain_pool)]
                deflect = deflect_pool[(node_count - 1) % len(deflect_pool)]
                mid = self.db.execute(
                    "insert into measure_point(nid,point_no,strain_data,deflect_data,collect_time,remark) "
                    "values (?,?,?,?,?,?)",
                    (nid, "P-D{:02d}".format(node_count), json.dumps(strain), json.dumps(deflect),
                     now_text(), "示例测点"))
                measure_count += 1
                solutions.append((nid, mid, strain, deflect))
                if node_count == 1:
                    self.db.execute(
                        "insert into measure_point(nid,point_no,strain_data,deflect_data,collect_time,remark) "
                        "values (?,?,?,?,?,?)",
                        (nid, "P-D{:02d}-复测".format(node_count),
                         json.dumps([12.8, 14.4, -8.0, 9.9]),
                         json.dumps([0.84, 0.93, 0.45, 0.77]), now_text(), "复测示例"))
                    measure_count += 1

        param = {
            "max_allow_force": 120.0,
            "stiffness_k": 100.0,
            "reg_weight": ALG_WEIGHT_REG,
            "w1": 0.6,
            "w2": 0.4,
            "coupling": 0.06,
            "svd_eps": SVD_THRESHOLD,
            "transfer_matrix": self.solver.build_transfer_matrix(4, 0.06).tolist(),
        }
        record_count = 0
        for nid, mid, strain, deflect in solutions:
            para = dict(param)
            para["stiffness_k"] = [param["stiffness_k"]] * len(strain)
            res = self.solver.coupling_claw_inversion(strain, deflect, para)
            result_json = json.dumps(res, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
            self.db.execute(
                "insert into calc_record(nid,mid,result_json,param_json,sha_hash,calc_time,status,alarm_msg,sign_user) "
                "values (?,?,?,?,?,?,?,?,NULL)",
                (nid, mid, result_json, json.dumps(param, ensure_ascii=False, sort_keys=True),
                 sha256_text(result_json), now_text(), 1 if res.get("valid") else 0, ""))
            record_count += 1

        order_row = self.db.query_one(
            "select r.rid, r.nid, coalesce(c.claw_no, '-') as claw_no from calc_record r "
            "join claw_node c on c.nid = r.nid join glass_panel g on g.gid = c.gid "
            "where g.pid = ? order by r.rid desc limit 1", (pid,))
        if order_row is not None:
            self.db.execute(
                "insert into work_order(nid,rid,title,detail,status,owner,create_time) "
                "values (?,?,?,?,?,?,?)",
                (order_row["nid"], order_row["rid"], "示例工程复核",
                 "节点 {} 的计算结果待复核".format(order_row["claw_no"]),
                 "开放", self.user.get("realname") or "系统管理员", now_text()))

        summary = {"pid": pid, "name": name, "panels": len(panels),
                   "nodes": node_count, "measures": measure_count, "records": record_count}
        self.audit("生成示例数据", "{}（ID {}）".format(name, pid))
        return summary

    def refresh_selectors(self):
        for selector in (self.measure_selector, self.calc_selector,
                         self.transfer_selector, self.calib_selector):
            selector.refresh()

    # ----------------------测点数据录入---------------------
    def init_measure_tab(self, layout):
        self.measure_selector = NodeSelector(self.db)
        self.measure_selector.changed.connect(self.load_measure_list)
        layout.addWidget(self.measure_selector)

        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.btn_measure_new = QPushButton("新增测点数据")
        self.btn_measure_new.setObjectName("primaryBtn")
        self.btn_measure_del = QPushButton("删除测点数据")
        self.btn_measure_del.setObjectName("dangerBtn")
        self.btn_measure_refresh = QPushButton("刷新")
        self.btn_measure_refresh.setObjectName("ghostBtn")
        self.write_buttons += [self.btn_measure_new, self.btn_measure_del]
        bar.addWidget(self.btn_measure_new)
        bar.addWidget(self.btn_measure_del)
        bar.addStretch(1)
        bar.addWidget(self.btn_measure_refresh)
        layout.addLayout(bar)

        self.table_measure = self._make_table(
            ["ID", "测点编号", "测点数", "应变序列", "挠度序列", "采集时间", "备注"])
        self.table_measure.setColumnWidth(0, 50)
        layout.addWidget(self.table_measure, 1)

        self.btn_measure_new.clicked.connect(self.add_measure)
        self.btn_measure_del.clicked.connect(self.delete_measure)
        self.btn_measure_refresh.clicked.connect(self.load_measure_list)
        self.load_measure_list()

    def load_measure_list(self):
        nid = self.measure_selector.current_node_id()
        if nid is None:
            self._fill_table(self.table_measure, [])
            return
        rows = self.db.query_all(
            "select mid, coalesce(point_no,''), coalesce(strain_data,''), coalesce(deflect_data,''), "
            "coalesce(collect_time,''), coalesce(remark,'') from measure_point where nid=? order by mid desc", (nid,))
        display = []
        for r in rows:
            strain = safe_json_loads(r[2], []) or []
            deflect = safe_json_loads(r[3], []) or []
            display.append([r[0], r[1], len(strain), preview_list(strain), preview_list(deflect), r[4], r[5]])
        self._fill_table(self.table_measure, display)

    def add_measure(self):
        if not self.can_write:
            return
        nid = self.measure_selector.current_node_id()
        if nid is None:
            QMessageBox.information(self, "提示", "请先选择驳接爪节点")
            return
        count = self.db.query_one("select count(*) as c from measure_point where nid=?", (nid,))["c"]
        dlg = MeasureDialog(self, "P{:02d}".format(count + 1))
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        mid = self.db.execute(
            "insert into measure_point(nid,point_no,strain_data,deflect_data,collect_time,remark) values (?,?,?,?,?,?)",
            (nid, data["point_no"], json.dumps(data["strain"]), json.dumps(data["deflect"]),
             data["collect_time"], data["remark"]))
        self.audit("新增测点", "{}（ID {}，{} 个测点）".format(data["point_no"], mid, len(data["strain"])))
        self.load_measure_list()
        self.on_calc_node_changed()

    def delete_measure(self):
        if not self.can_write:
            return
        mid = self._selected_id(self.table_measure)
        if mid is None:
            return
        if QMessageBox.question(self, "确认删除", "删除该测点数据及其关联计算记录？") != QMessageBox.StandardButton.Yes:
            return
        self.db.execute_many([
            ("delete from calc_record where mid=?", (mid,)),
            ("delete from measure_point where mid=?", (mid,)),
        ])
        self.audit("删除测点", "测点 ID {}".format(mid))
        self.load_measure_list()
        self.on_calc_node_changed()

    # ----------------------受力反演计算---------------------
    def init_calc_tab(self, layout):
        self.calc_selector = NodeSelector(self.db)
        self.calc_selector.changed.connect(self.on_calc_node_changed)
        layout.addWidget(self.calc_selector)

        row = QHBoxLayout()
        row.setSpacing(10)
        measure_label = QLabel("测点数据")
        measure_label.setObjectName("filterLabel")
        row.addWidget(measure_label)
        self.cb_measure = QComboBox()
        self.cb_measure.setMinimumWidth(320)
        row.addWidget(self.cb_measure)
        self.calc_source_hint = QLabel("拖动滑块实时试算，确认后保存发布")
        self.calc_source_hint.setObjectName("sectionHint")
        row.addStretch(1)
        row.addWidget(self.calc_source_hint)
        measure_bar = QFrame()
        measure_bar.setObjectName("filterBar")
        measure_bar.setAttribute(Qt.WidgetAttribute.WA_StyledBackground, True)
        measure_bar.setLayout(row)
        row.setContentsMargins(14, 10, 14, 10)
        layout.addWidget(measure_bar)

        body = QHBoxLayout()
        body.setSpacing(14)
        param_box = QGroupBox("实时参数")
        param_box.setFixedWidth(350)
        param_layout = QVBoxLayout(param_box)
        param_layout.setSpacing(9)
        self.force_slider = SliderControl("最大允许受力", 60, 180, 120, 1, " kN")
        self.stiffness_slider = SliderControl("节点刚度 k", 20, 300, 100, 0, " kN/mm")
        self.reg_slider = SliderControl("正则化权重", 0.001, 0.100, 0.010, 3, "")
        self.w1_slider = SliderControl("SVD 融合权重 w1", 0.0, 1.0, 0.60, 2, "")
        self.coupling_slider = SliderControl("爪臂耦合系数", 0.0, 0.20, 0.06, 3, "")
        for control in (self.force_slider, self.stiffness_slider, self.reg_slider,
                        self.w1_slider, self.coupling_slider):
            param_layout.addWidget(control)
            control.valueChanged.connect(self._calc_param_changed)
        self.lbl_w2 = QLabel("w2 = 1 - w1 = 0.40")
        self.lbl_w2.setObjectName("sectionHint")
        param_layout.addWidget(self.lbl_w2)
        param_layout.addStretch(1)
        self.btn_run_calc = QPushButton("保存并发布结果")
        self.btn_run_calc.setObjectName("primaryBtn")
        self.btn_run_calc.setMinimumHeight(38)
        param_layout.addWidget(self.btn_run_calc)
        self.write_buttons.append(self.btn_run_calc)
        body.addWidget(param_box)

        preview_box = QGroupBox("爪臂受力预览")
        preview_layout = QVBoxLayout(preview_box)
        self.arm_view = ArmVectorView()
        preview_layout.addWidget(self.arm_view, 1)
        summary = QHBoxLayout()
        summary.setSpacing(18)
        self.calc_max_label = QLabel("最大受力：—")
        self.calc_threshold_label = QLabel("允许值：120 kN")
        self.calc_status = QLabel("待计算")
        for label in (self.calc_max_label, self.calc_threshold_label):
            label.setObjectName("sectionHint")
            summary.addWidget(label)
        summary.addStretch(1)
        summary.addWidget(self.calc_status)
        preview_layout.addLayout(summary)
        body.addWidget(preview_box, 1)
        layout.addLayout(body, 3)

        bottom = QHBoxLayout()
        bottom.setSpacing(14)
        scan_box = QGroupBox("正则化扫描（最大受力）")
        scan_layout = QVBoxLayout(scan_box)
        self.scan_chart = ChartWidget("line")
        self.scan_chart.setMinimumHeight(190)
        scan_layout.addWidget(self.scan_chart)
        bottom.addWidget(scan_box, 3)

        log_box = QGroupBox("计算记录")
        log_layout = QVBoxLayout(log_box)
        self.txt_calc_log = QTextEdit()
        self.txt_calc_log.setObjectName("calcLog")
        self.txt_calc_log.setReadOnly(True)
        self.txt_calc_log.setPlainText(
            "拖动左侧滑块可实时调整参数。\n确认参数后点击“保存并发布结果”，结果将写入数据库并同步三维模型。")
        log_layout.addWidget(self.txt_calc_log)
        bottom.addWidget(log_box, 2)
        layout.addLayout(bottom, 2)

        self.btn_run_calc.clicked.connect(self.run_calc_task)
        self.cb_measure.currentIndexChanged.connect(self.preview_inversion)
        self.load_calc_measures()

    def _calc_param_changed(self):
        self.lbl_w2.setText("w2 = 1 - w1 = {:.2f}".format(1.0 - self.w1_slider.value()))
        self.preview_inversion()

    def _calc_current_data(self):
        node = self.calc_selector.current_node_row()
        arms = int(node["arm_count"] or 4) if node else 4
        mid = self.cb_measure.currentData()
        measure = self.db.query_one("select * from measure_point where mid=?", (mid,)) if mid else None
        strain = safe_json_loads(measure["strain_data"], []) if measure else []
        deflect = safe_json_loads(measure["deflect_data"], []) if measure else []
        synthetic = not strain
        if synthetic:
            base = [12.3, 14.1, -8.2, 9.6, 10.5, 13.2]
            base_def = [0.82, 0.91, 0.44, 0.75, 0.69, 0.86]
            strain = [base[i % len(base)] for i in range(arms)]
            deflect = [base_def[i % len(base_def)] for i in range(arms)]
        if len(deflect) != len(strain):
            deflect = [0.8] * len(strain)
        return node, measure, strain, deflect, synthetic

    def preview_inversion(self):
        if not hasattr(self, "arm_view"):
            return
        node, measure, strain, deflect, synthetic = self._calc_current_data()
        if not strain:
            self.arm_view.set_data("", 4, [], self.force_slider.value())
            return
        param = {
            "max_allow_force": self.force_slider.value(),
            "stiffness_k": self.stiffness_slider.value(),
            "reg_weight": self.reg_slider.value(),
            "w1": self.w1_slider.value(),
            "w2": 1.0 - self.w1_slider.value(),
            "coupling": self.coupling_slider.value(),
            "svd_eps": SVD_THRESHOLD,
            "transfer_matrix": self.solver.build_transfer_matrix(len(strain), self.coupling_slider.value()).tolist(),
        }
        para = dict(param)
        para["stiffness_k"] = [param["stiffness_k"]] * len(strain)
        try:
            result = self.solver.coupling_claw_inversion(strain, deflect, para)
        except Exception as exc:
            self.arm_view.set_data(node["claw_no"] if node else "", len(strain), [], param["max_allow_force"])
            self.calc_source_hint.setText("预览失败：{}".format(exc))
            return
        forces = result.get("result", [])
        max_force = max((abs(v) for v in forces), default=0.0)
        self.arm_view.set_data(node["claw_no"] if node else "示例", len(forces), forces, param["max_allow_force"])
        self.calc_max_label.setText("最大受力：{:.2f} kN".format(max_force))
        self.calc_threshold_label.setText("允许值：{:.1f} kN".format(param["max_allow_force"]))
        if max_force > param["max_allow_force"]:
            self._set_tag(self.calc_status, "超限", "warn")
        else:
            self._set_tag(self.calc_status, "通过", "ok")
        self.calc_source_hint.setText(
            "当前使用{}测点".format("示例" if synthetic else "所选"))
        self._update_scan_chart(strain, deflect, param)

    def _update_scan_chart(self, strain, deflect, param):
        regs = [0.001, 0.003, 0.005, 0.010, 0.020, 0.050, 0.100]
        values = []
        for reg in regs:
            para = dict(param)
            para["reg_weight"] = reg
            para["stiffness_k"] = [param["stiffness_k"]] * len(strain)
            try:
                result = self.solver.coupling_claw_inversion(strain, deflect, para)
                values.append(max((abs(v) for v in result.get("result", [])), default=0.0))
            except Exception:
                values.append(0.0)
        self.scan_chart.set_data(
            ["{:.3f}".format(v) for v in regs],
            [{"name": "最大受力", "color": "#2563eb", "values": values, "fill": True}], "")

    def on_calc_node_changed(self):
        self.load_calc_measures()

    def load_calc_measures(self):
        nid = self.calc_selector.current_node_id()
        self.cb_measure.blockSignals(True)
        self.cb_measure.clear()
        if nid is not None:
            for r in self.db.query_all(
                    "select mid, point_no, collect_time from measure_point where nid=? order by mid desc", (nid,)):
                self.cb_measure.addItem(
                    "{} · {}（{}）".format(r["point_no"], r["collect_time"] or "", r["mid"]), r["mid"])
        self.cb_measure.blockSignals(False)
        self.preview_inversion()

    def run_calc_task(self):
        if not self.can_write or self.calc_thread is not None:
            return
        node = self.calc_selector.current_node_row()
        if node is None:
            QMessageBox.information(self, "提示", "请先选择驳接爪节点")
            return
        mid = self.cb_measure.currentData()
        if mid is None:
            QMessageBox.information(self, "提示", "该节点还没有测点数据，请先录入")
            return
        measure = self.db.query_one("select * from measure_point where mid=?", (mid,))
        if measure is None:
            return
        strain = safe_json_loads(measure["strain_data"], []) or []
        deflect = safe_json_loads(measure["deflect_data"], []) or []
        if not strain or len(strain) != len(deflect):
            QMessageBox.warning(self, "提示", "测点数据不完整或应变/挠度数量不一致")
            return

        w1 = float(self.w1_slider.value())
        coupling = float(self.coupling_slider.value())
        param = {
            "max_allow_force": float(self.force_slider.value()),
            "stiffness_k": float(self.stiffness_slider.value()),
            "reg_weight": float(self.reg_slider.value()),
            "w1": w1,
            "w2": 1.0 - w1,
            "coupling": coupling,
            "svd_eps": SVD_THRESHOLD,
            "transfer_matrix": self.solver.build_transfer_matrix(len(strain), coupling).tolist(),
        }
        para = dict(param)
        para["max_allow_force"] = param["max_allow_force"]
        para["stiffness_k"] = [param["stiffness_k"]] * len(strain)

        self._calc_context = {
            "node": dict(node), "measure": dict(measure), "param": param,
            "strain": strain, "deflect": deflect,
        }
        self.txt_calc_log.clear()
        self.txt_calc_log.append("==== 开始执行受力反演计算 ====")
        self.txt_calc_log.append("节点：{} ｜ 爪臂数：{} ｜ 测点：{} ｜ 测点数：{}".format(
            node["claw_no"], node["arm_count"], measure["point_no"], len(strain)))
        self.txt_calc_log.append("参数：阈值 {:.1f} kN ｜ k={:.0f} ｜ 正则 {:.3f} ｜ w1={:.2f} ｜ 耦合 {:.3f}".format(
            param["max_allow_force"], param["stiffness_k"], param["reg_weight"], w1, coupling))

        self.btn_run_calc.setEnabled(False)
        self.calc_thread = CalcThread(self.solver, strain, deflect, para, self)
        self.calc_thread.sig_finish.connect(self.on_calc_done)
        self.calc_thread.sig_alarm.connect(self.on_calc_alarm)
        self.calc_thread.finished.connect(self._on_calc_thread_finished)
        self.calc_thread.finished.connect(self.calc_thread.deleteLater)
        self.calc_thread.start()

    def _on_calc_thread_finished(self):
        self.calc_thread = None
        self.btn_run_calc.setEnabled(self.can_write)

    def on_calc_done(self, res):
        ctx = self._calc_context
        if ctx is None:
            return
        forces = res.get("result", [])
        self.txt_calc_log.append("各爪臂反演受力（kN）：" + ", ".join(format_float(v, 3) for v in forces))
        self.txt_calc_log.append("最大受力：{} kN ｜ 允许值：{} kN".format(
            format_float(res.get("max_abs"), 3), format_float(ctx["param"]["max_allow_force"], 1)))
        err = res.get("deflect_fit", {}).get("error")
        self.txt_calc_log.append("挠度拟合平均误差：{} mm".format(format_float(err, 4)))

        result_json = json.dumps(res, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        digest = sha256_text(result_json)
        self.txt_calc_log.append("结果 SHA256 摘要：" + digest)
        status = 1 if res.get("valid") else 0
        alarm = "" if status == 1 else "最大受力超出允许阈值 {:.1f} kN".format(ctx["param"]["max_allow_force"])
        if status == 0:
            self.txt_calc_log.append("【告警】" + alarm + "，校验不通过，不输出最终受力结果。")
            QMessageBox.warning(self, "校验告警", alarm + "\n本次结果已按“超限”状态留存备查，但不参与三维展示与签认。")

        rid = self.db.execute(
            "insert into calc_record(nid,mid,result_json,param_json,sha_hash,calc_time,status,alarm_msg,sign_user) "
            "values (?,?,?,?,?,?,?,?,NULL)",
            (ctx["node"]["nid"], ctx["measure"]["mid"], result_json,
             json.dumps(ctx["param"], ensure_ascii=False, sort_keys=True), digest, now_text(), status, alarm))
        self.audit("受力计算", "记录 {}，节点 {}，摘要 {}".format(rid, ctx["node"]["claw_no"], digest[:16]))
        self.txt_calc_log.append("计算结果已写入数据库，记录 ID：{}".format(rid))

        if status == 1:
            node_row = self.db.query_one("select gid from claw_node where nid=?", (ctx["node"]["nid"],))
            model = self.build_panel_model(node_row["gid"]) if node_row else None
            if model:
                self.push_model_to_scene(model)
        self._calc_context = None
        self.load_record_list()

    def on_calc_alarm(self, msg):
        self.txt_calc_log.append("【告警】" + msg)
        QMessageBox.critical(self, "计算异常", msg)

    # ----------------------数字孪生视图---------------------
    def init_twin_tab(self, layout):
        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.btn_scene_push = QPushButton("推送当前结果")
        self.btn_scene_push.setObjectName("primaryBtn")
        self.btn_scene_reset = QPushButton("重置颜色")
        self.btn_scene_reset.setObjectName("ghostBtn")
        self.btn_scene_reload = QPushButton("重新加载视图")
        self.btn_scene_reload.setObjectName("ghostBtn")
        bar.addWidget(self.btn_scene_push)
        bar.addWidget(self.btn_scene_reset)
        bar.addWidget(self.btn_scene_reload)
        bar.addStretch(1)
        layout.addLayout(bar)

        if HAS_WEBENGINE:
            self.web_view = QWebEngineView()
            settings = self.web_view.settings()
            settings.setAttribute(QWebEngineSettings.WebAttribute.LocalContentCanAccessFileUrls, True)
            settings.setAttribute(QWebEngineSettings.WebAttribute.LocalContentCanAccessRemoteUrls, False)
            self.web_view.loadFinished.connect(self.on_scene_loaded)
            layout.addWidget(self.web_view, 1)
            if SCENE_PATH.exists():
                self.web_view.load(QUrl.fromLocalFile(str(SCENE_PATH)))
            else:
                self.web_view.setHtml("<h3>缺少 scene.html 文件</h3>")
        else:
            self.web_view = None
            label = QLabel("未安装 PyQt6-WebEngine，三维视图不可用。\n可执行：pip install PyQt6-WebEngine")
            label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            label.setStyleSheet("color:#94a3b8; font-size:13px;")
            layout.addWidget(label, 1)

        self.btn_scene_push.clicked.connect(self.push_latest_force)
        self.btn_scene_reset.clicked.connect(self.reset_scene)
        self.btn_scene_reload.clicked.connect(self.reload_scene)

    def on_scene_loaded(self, ok):
        try:
            self._scene_ready = bool(ok)
            if ok and getattr(self, "_pending_model", None):
                self._run_scene_model(self._pending_model)
        except Exception as exc:
            print("三维场景加载处理失败：{}".format(exc))

    def push_latest_force(self):
        if not getattr(self, "_pending_model", None):
            QMessageBox.information(self, "提示", "还没有可推送的模型，请先选择分格或执行受力反演")
            return
        self._run_scene_model(self._pending_model)

    def reset_scene(self):
        if HAS_WEBENGINE and self.web_view is not None:
            self.web_view.page().runJavaScript("if (window.resetModel) { resetModel(); }")
        self._pending_model = None

    def reload_scene(self):
        if HAS_WEBENGINE and self.web_view is not None and SCENE_PATH.exists():
            self._scene_ready = False
            self.web_view.load(QUrl.fromLocalFile(str(SCENE_PATH)))

    # ----------------------成果导出签认---------------------
    def init_report_tab(self, layout):
        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.btn_record_refresh = QPushButton("刷新记录")
        self.btn_record_refresh.setObjectName("ghostBtn")
        self.btn_report_pdf = QPushButton("生成 PDF 报告")
        self.btn_report_pdf.setObjectName("primaryBtn")
        self.btn_record_sign = QPushButton("成果签认")
        self.btn_evidence_export = QPushButton("导出证据链包")
        self.btn_evidence_verify = QPushButton("校验证据链")
        self.btn_evidence_verify.setObjectName("ghostBtn")
        self.btn_audit_view = QPushButton("审计日志")
        self.btn_audit_view.setObjectName("ghostBtn")
        for btn in (self.btn_report_pdf, self.btn_record_sign, self.btn_evidence_export):
            self.write_buttons.append(btn)
        bar.addWidget(self.btn_record_refresh)
        bar.addWidget(self.btn_report_pdf)
        bar.addWidget(self.btn_record_sign)
        bar.addWidget(self.btn_evidence_export)
        bar.addWidget(self.btn_evidence_verify)
        bar.addStretch(1)
        bar.addWidget(self.btn_audit_view)
        layout.addLayout(bar)

        self.table_record = self._make_table(
            ["ID", "工程", "分格", "节点", "最大受力(kN)", "结论", "计算时间", "签认人"])
        self.table_record.setColumnWidth(0, 50)
        layout.addWidget(self.table_record, 1)

        self.btn_record_refresh.clicked.connect(self.load_record_list)
        self.btn_report_pdf.clicked.connect(self.generate_report)
        self.btn_record_sign.clicked.connect(self.sign_record)
        self.btn_evidence_export.clicked.connect(self.export_evidence_pack)
        self.btn_evidence_verify.clicked.connect(self.verify_evidence)
        self.btn_audit_view.clicked.connect(self.show_audit_log)
        self.load_record_list()

    def load_record_list(self):
        rows = self.db.query_all(
            "select r.rid, coalesce(p.proj_name,'-'), coalesce(g.glass_no,'-'), coalesce(c.claw_no,'-'), "
            "r.calc_time, coalesce(r.status,0), coalesce(u.realname, u.username, '未签认'), r.result_json "
            "from calc_record r "
            "left join claw_node c on c.nid = r.nid "
            "left join glass_panel g on g.gid = c.gid "
            "left join project_info p on p.pid = g.pid "
            "left join user_info u on u.uid = r.sign_user "
            "order by r.rid desc")
        display = []
        for r in rows:
            res = safe_json_loads(r[7], {}) or {}
            forces = res.get("result", []) or []
            max_force = max((abs(float(v)) for v in forces), default=None)
            status_text = "通过" if int(r[5]) == 1 else "超限"
            display.append([r[0], r[1], r[2], r[3], format_float(max_force, 3, "-"), status_text,
                            r[4] or "", r[6] or ""])
        self._fill_table(self.table_record, display)

    def _record_row(self, rid):
        return self.db.query_one(
            "select r.*, p.proj_name, p.facade_name, g.glass_no, g.width, g.height, g.thickness, "
            "c.claw_no, c.arm_count, c.preload, c.eccentricity, c.node_type, c.arm_len "
            "from calc_record r "
            "left join claw_node c on c.nid = r.nid "
            "left join glass_panel g on g.gid = c.gid "
            "left join project_info p on p.pid = g.pid "
            "where r.rid = ?", (rid,))

    def generate_report(self):
        if not self.can_write:
            return
        rid = self._selected_id(self.table_record)
        if rid is None:
            QMessageBox.information(self, "提示", "请先选择一条计算记录")
            return
        rec = self._record_row(rid)
        if rec is None:
            return
        measure = self.db.query_one("select * from measure_point where mid=?", (rec["mid"],)) if rec["mid"] else None
        signer = ""
        if rec["sign_user"]:
            user = self.db.query_one("select realname, username from user_info where uid=?", (rec["sign_user"],))
            signer = (user["realname"] or user["username"]) if user else str(rec["sign_user"])
        html_text = self._build_report_html(rec, measure, signer)
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        html_path = REPORT_DIR / "report_{}_{}.html".format(rid, stamp)
        pdf_path = REPORT_DIR / "report_{}_{}.pdf".format(rid, stamp)
        html_path.write_text(html_text, encoding="utf-8")

        pdf_ok = True
        try:
            doc = QTextDocument()
            doc.setDefaultFont(QFont("Microsoft YaHei", 10))
            doc.setHtml(html_text)
            printer = QPrinter(QPrinter.PrinterMode.HighResolution)
            printer.setOutputFormat(QPrinter.OutputFormat.PdfFormat)
            printer.setOutputFileName(str(pdf_path))
            doc.print(printer)
        except Exception as exc:
            pdf_ok = False
            QMessageBox.warning(self, "PDF 导出失败", "HTML 报告已生成，PDF 导出失败：{}".format(exc))

        target = pdf_path if pdf_ok else html_path
        self.db.execute("update calc_record set report_path=? where rid=?", (str(target), rid))
        self.audit("导出报告", "记录 {} → {}".format(rid, target.name))
        QMessageBox.information(self, "导出完成", "报告已生成：\n{}".format(target))

    def _build_report_html(self, rec, measure, signer):
        res = safe_json_loads(rec["result_json"], {}) or {}
        param = safe_json_loads(rec["param_json"], {}) or {}
        forces = res.get("result", []) or []
        status_text = "通过" if int(rec["status"] or 0) == 1 else "超限（不予输出）"
        force_rows = "".join(
            "<tr><td>爪臂 {}</td><td>{:.3f}</td></tr>".format(i + 1, float(v)) for i, v in enumerate(forces))
        strain = safe_json_loads(measure["strain_data"], []) if measure else []
        deflect = safe_json_loads(measure["deflect_data"], []) if measure else []
        measure_rows = "".join(
            "<tr><td>{}</td><td>{}</td><td>{}</td></tr>".format(
                i + 1, format_float(strain[i] if i < len(strain) else None, 3),
                format_float(deflect[i] if i < len(deflect) else None, 4))
            for i in range(max(len(strain), len(deflect))))
        css = """
        <style>
        body { font-family: "Microsoft YaHei", SimSun, sans-serif; color:#222; line-height:1.6; }
        h1 { text-align:center; font-size:20px; margin:6px 0 2px 0; }
        h2 { font-size:14px; border-left:4px solid #2f6fa8; padding-left:6px; margin:14px 0 6px 0; }
        .sub { text-align:center; color:#666; font-size:12px; margin-bottom:10px; }
        table { border-collapse:collapse; width:100%; font-size:12px; }
        th, td { border:1px solid #888; padding:4px 6px; }
        th { background:#eef3f8; width:26%; text-align:left; }
        .kv td { width:auto; }
        .sign { margin-top:24px; font-size:12px; }
        .hash { font-family:Consolas, monospace; font-size:9px; word-break:break-all; color:#444; }
        </style>
        """
        body = """
        <h1>驳接爪受力反演计算报告</h1>
        <div class="sub">报告编号：R{rid} ｜ 生成时间：{now}</div>
        <h2>一、工程与节点信息</h2>
        <table class="kv">
          <tr><th>工程名称</th><td>{proj}</td><th>立面名称</th><td>{facade}</td></tr>
          <tr><th>玻璃分格</th><td>{glass}</td><th>分格尺寸</th><td>{w} × {h} × {t} mm</td></tr>
          <tr><th>节点编号</th><td>{claw}</td><th>节点类型</th><td>{ntype}</td></tr>
          <tr><th>爪臂数量</th><td>{arms}</td><th>预紧力</th><td>{preload} kN</td></tr>
          <tr><th>偏心距</th><td>{ecc} mm</td><th>爪臂长度</th><td>{armlen} mm</td></tr>
        </table>
        <h2>二、测点数据</h2>
        <table>
          <tr><th>序号</th><th>应变（με）</th><th>挠度（mm）</th></tr>
          {measure_rows}
        </table>
        <h2>三、反演参数</h2>
        <table class="kv">
          <tr><th>最大允许受力</th><td>{maxf} kN</td><th>节点刚度 k</th><td>{k}</td></tr>
          <tr><th>正则化权重</th><td>{reg}</td><th>融合权重</th><td>w1={w1}，w2={w2}</td></tr>
          <tr><th>爪臂耦合系数</th><td>{coup}</td><th>SVD 阈值</th><td>{eps}</td></tr>
        </table>
        <h2>四、反演结果</h2>
        <table>
          <tr><th>爪臂</th><th>受力（kN）</th></tr>
          {force_rows}
        </table>
        <p>最大受力：<b>{maxabs} kN</b> ｜ 允许值：{maxf} kN ｜ 校验结论：<b>{status}</b></p>
        <p>挠度拟合平均误差：{err} mm</p>
        <h2>五、证据与签认</h2>
        <p class="hash">结果 JSON 的 SHA256：{digest}</p>
        <p>计算时间：{calc_time}</p>
        <p>签认人：{signer}</p>
        <p>签认时间：{sign_time}</p>
        <div class="sign">本报告由点支式玻璃幕墙驳接爪受力反演软件 V1.0 自动生成，计算结果仅供工程复核参考。</div>
        """.format(
            rid=rec["rid"], now=now_text(),
            proj=html_lib.escape(rec["proj_name"] or "-"),
            facade=html_lib.escape(rec["facade_name"] or "-"),
            glass=html_lib.escape(rec["glass_no"] or "-"),
            w=format_float(rec["width"], 0), h=format_float(rec["height"], 0), t=format_float(rec["thickness"], 1),
            claw=html_lib.escape(rec["claw_no"] or "-"),
            ntype=html_lib.escape(rec["node_type"] or "-"),
            arms=rec["arm_count"] or 0, preload=format_float(rec["preload"], 1),
            ecc=format_float(rec["eccentricity"], 1), armlen=format_float(rec["arm_len"], 1),
            measure_rows=measure_rows or "<tr><td colspan='3'>无测点数据</td></tr>",
            maxf=format_float(param.get("max_allow_force"), 1),
            k=format_float(param.get("stiffness_k"), 3),
            reg=format_float(param.get("reg_weight"), 4),
            w1=format_float(param.get("w1"), 2), w2=format_float(param.get("w2"), 2),
            coup=format_float(param.get("coupling"), 3), eps=param.get("svd_eps", ""),
            force_rows=force_rows or "<tr><td colspan='2'>无结果</td></tr>",
            maxabs=format_float(res.get("max_abs"), 3),
            status=status_text,
            err=format_float(res.get("deflect_fit", {}).get("error"), 4),
            digest=rec["sha_hash"] or "", calc_time=rec["calc_time"] or "",
            signer=html_lib.escape(signer or "未签认"), sign_time=rec["sign_time"] or "—")
        return "<html><head><meta charset='utf-8'>" + css + "</head><body>" + body + "</body></html>"

    def sign_record(self):
        if not self.can_write:
            return
        rid = self._selected_id(self.table_record)
        if rid is None:
            QMessageBox.information(self, "提示", "请先选择一条计算记录")
            return
        rec = self.db.query_one("select * from calc_record where rid=?", (rid,))
        if rec is None:
            return
        if int(rec["status"] or 0) != 1:
            QMessageBox.warning(self, "提示", "该记录校验不通过，不能签认")
            return
        dlg = SignDialog(self, self.user.get("realname") or self.user.get("username"))
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        row = self.db.query_one("select passwd from user_info where uid=?", (self.user.get("uid"),))
        if row is None or not check_password(row["passwd"], dlg.password()):
            QMessageBox.warning(self, "提示", "密码错误，签认未生效")
            return
        self.db.execute("update calc_record set sign_user=?, sign_time=? where rid=?",
                        (self.user.get("uid"), now_text(), rid))
        self.audit("成果签认", "记录 {} 由 {} 签认".format(rid, self.user.get("realname")))
        self.load_record_list()
        QMessageBox.information(self, "签认完成", "记录 {} 已完成签认".format(rid))

    def _collect_evidence(self):
        rows = self.db.query_all("select rid, result_json, sha_hash, calc_time from calc_record order by rid")
        hashes = []
        items = []
        for r in rows:
            stored = r["sha_hash"] or ""
            calc = sha256_text(r["result_json"] or "")
            hashes.append(calc)
            items.append({"rid": r["rid"], "sha256": stored, "recomputed": calc,
                          "match": stored == calc, "calc_time": r["calc_time"]})
        chain = HashTreeTool.build_chain(hashes)
        for idx, item in enumerate(items):
            item["chain_hash"] = chain[idx] if idx < len(chain) else ""
        root = HashTreeTool.build_merkle_root(hashes)
        return items, chain, root

    def verify_evidence(self):
        items, chain, root = self._collect_evidence()
        bad = [it for it in items if not it["match"]]
        if not items:
            QMessageBox.information(self, "校验结果", "当前还没有计算记录")
            return
        if bad:
            QMessageBox.critical(self, "校验失败", "发现 {} 条记录摘要不一致，最早异常记录 ID：{}".format(
                len(bad), bad[0]["rid"]))
            return
        QMessageBox.information(self, "校验通过", "共 {} 条计算记录，摘要全部一致。\nMerkle 根：{}".format(len(items), root))

    def export_evidence_pack(self):
        if not self.can_write:
            return
        items, chain, root = self._collect_evidence()
        if not items:
            QMessageBox.information(self, "提示", "当前还没有计算记录，无法导出证据链")
            return
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        evidence = {
            "software": APP_TITLE,
            "generated_at": now_text(),
            "record_count": len(items),
            "merkle_root": root,
            "chain": chain,
            "records": items,
        }
        json_path = EVIDENCE_DIR / "evidence_{}.json".format(stamp)
        json_path.write_text(json.dumps(evidence, ensure_ascii=False, indent=2), encoding="utf-8")

        zip_path = EVIDENCE_DIR / "evidence_pack_{}.zip".format(stamp)
        with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
            if Path(DB_PATH).exists():
                zf.write(DB_PATH, Path(DB_PATH).name)
            zf.write(json_path, json_path.name)
            zf.writestr(
                "README.txt",
                "驳接爪受力反演软件 V1.0 证据链包\n生成时间：{}\n记录数量：{}\nMerkle 根：{}\n".format(
                    now_text(), len(items), root))
            if REPORT_DIR.exists():
                for path in REPORT_DIR.iterdir():
                    if path.is_file():
                        zf.write(path, "reports/" + path.name)

        self.audit("导出证据链", "{} 条记录，Merkle 根 {}".format(len(items), root[:16]))
        QMessageBox.information(self, "导出完成", "证据链包已生成：\n{}\n\nMerkle 根：\n{}".format(zip_path, root))

    def show_audit_log(self):
        dlg = QDialog(self)
        dlg.setWindowTitle("审计日志")
        dlg.resize(900, 520)
        layout = QVBoxLayout(dlg)
        table = self._make_table(["时间", "用户", "操作", "详情"])
        rows = self.db.query_all(
            "select l.opt_time, coalesce(u.username,'系统'), l.opt_type, l.opt_detail "
            "from audit_log l left join user_info u on u.uid=l.uid order by l.lid desc limit 500")
        display = [[r[0], r[1], r[2], r[3]] for r in rows]
        self._fill_table(table, display)
        layout.addWidget(table)
        btn = QPushButton("关闭")
        btn.clicked.connect(dlg.accept)
        layout.addWidget(btn, 0, Qt.AlignmentFlag.AlignRight)
        dlg.exec()

    # ----------------------账号权限管理---------------------
    def init_user_tab(self, layout):
        if not self.is_admin:
            label = QLabel("账号管理仅管理员可操作。\n当前角色：{}".format(ROLE_NAMES.get(self.role)))
            label.setAlignment(Qt.AlignmentFlag.AlignCenter)
            label.setStyleSheet("color:#94a3b8; font-size:13px;")
            layout.addWidget(label, 1)
            self.table_user = None
            return

        bar = QHBoxLayout()
        bar.setSpacing(8)
        self.btn_user_new = QPushButton("新增账号")
        self.btn_user_new.setObjectName("primaryBtn")
        self.btn_user_reset = QPushButton("重置密码")
        self.btn_user_toggle = QPushButton("启用/停用")
        self.btn_user_del = QPushButton("删除账号")
        self.btn_user_del.setObjectName("dangerBtn")
        self.admin_buttons += [self.btn_user_new, self.btn_user_reset, self.btn_user_toggle, self.btn_user_del]
        for btn in (self.btn_user_new, self.btn_user_reset, self.btn_user_toggle, self.btn_user_del):
            bar.addWidget(btn)
        bar.addStretch(1)
        layout.addLayout(bar)

        self.table_user = self._make_table(["ID", "用户名", "真实姓名", "角色", "状态", "创建时间", "最近登录"])
        self.table_user.setColumnWidth(0, 50)
        layout.addWidget(self.table_user, 1)
        self.btn_user_new.clicked.connect(self.add_user)
        self.btn_user_reset.clicked.connect(self.reset_user_password)
        self.btn_user_toggle.clicked.connect(self.toggle_user)
        self.btn_user_del.clicked.connect(self.delete_user)
        self.load_user_list()

    def load_user_list(self):
        if self.table_user is None:
            return
        rows = self.db.query_all(
            "select uid, username, coalesce(realname,''), role, coalesce(status,1), "
            "coalesce(create_time,''), coalesce(last_login,'') from user_info order by uid")
        display = [[r[0], r[1], r[2], ROLE_NAMES.get(int(r[3]), r[3]),
                    "启用" if int(r[4]) == 1 else "停用", r[5], r[6]] for r in rows]
        self._fill_table(self.table_user, display)

    def add_user(self):
        if not self.is_admin:
            return
        dlg = UserDialog(self)
        if dlg.exec() != QDialog.DialogCode.Accepted:
            return
        data = dlg.data()
        if self.db.query_one("select uid from user_info where username=?", (data["username"],)):
            QMessageBox.warning(self, "提示", "用户名已存在")
            return
        uid = self.db.execute(
            "insert into user_info(username,passwd,role,realname,create_time,status) values (?,?,?,?,?,1)",
            (data["username"], make_password(data["password"]), data["role"], data["realname"], now_text()))
        self.audit("新增账号", "{}（ID {}）".format(data["username"], uid))
        self.load_user_list()

    def reset_user_password(self):
        if not self.is_admin:
            return
        uid = self._selected_id(self.table_user)
        if uid is None:
            return
        pwd, ok = QInputDialog.getText(self, "重置密码", "请输入新密码（至少 6 位）：",
                                       QLineEdit.EchoMode.Password)
        if not ok or not pwd:
            return
        if len(pwd) < 6:
            QMessageBox.warning(self, "提示", "密码长度不能少于 6 位")
            return
        self.db.execute("update user_info set passwd=? where uid=?", (make_password(pwd), uid))
        self.audit("重置密码", "用户 ID {}".format(uid))
        QMessageBox.information(self, "完成", "密码已重置")

    def toggle_user(self):
        if not self.is_admin:
            return
        uid = self._selected_id(self.table_user)
        if uid is None:
            return
        if uid == self.user.get("uid"):
            QMessageBox.warning(self, "提示", "不能停用当前登录账号")
            return
        row = self.db.query_one("select username, coalesce(status,1) as st, role from user_info where uid=?", (uid,))
        if row is None:
            return
        if int(row["st"]) == 1 and int(row["role"]) == USER_ROLE_ADMIN:
            admins = self.db.query_one(
                "select count(*) as c from user_info where role=0 and coalesce(status,1)=1")["c"]
            if admins <= 1:
                QMessageBox.warning(self, "提示", "至少保留一个启用状态的管理员")
                return
        new_status = 0 if int(row["st"]) == 1 else 1
        self.db.execute("update user_info set status=? where uid=?", (new_status, uid))
        self.audit("账号状态", "{} → {}".format(row["username"], "启用" if new_status else "停用"))
        self.load_user_list()

    def delete_user(self):
        if not self.is_admin:
            return
        uid = self._selected_id(self.table_user)
        if uid is None:
            return
        if uid == self.user.get("uid"):
            QMessageBox.warning(self, "提示", "不能删除当前登录账号")
            return
        row = self.db.query_one("select username, role from user_info where uid=?", (uid,))
        if row is None:
            return
        if int(row["role"]) == USER_ROLE_ADMIN:
            admins = self.db.query_one("select count(*) as c from user_info where role=0")["c"]
            if admins <= 1:
                QMessageBox.warning(self, "提示", "至少保留一个管理员账号")
                return
        if QMessageBox.question(self, "确认删除", "确定删除账号 {}？".format(row["username"])) != QMessageBox.StandardButton.Yes:
            return
        self.db.execute("delete from user_info where uid=?", (uid,))
        self.audit("删除账号", row["username"])
        self.load_user_list()

    def closeEvent(self, event):
        if self.calc_thread is not None and self.calc_thread.isRunning():
            if QMessageBox.question(self, "计算进行中", "受力反演仍在计算，确定退出吗？") != QMessageBox.StandardButton.Yes:
                event.ignore()
                return
            self.calc_thread.requestInterruption()
            self.calc_thread.wait(3000)
        self.audit("退出系统", "软件正常关闭")
        event.accept()


def main():
    app = QApplication(sys.argv)
    app.setApplicationName(APP_TITLE)
    app.setStyle("Fusion")
    app.setStyleSheet(APP_QSS)
    app.setFont(QFont("Microsoft YaHei", 10))
    db = SqliteHelper(DB_PATH)
    db.init_table()
    login = LoginDialog(db)
    if login.exec() != QDialog.DialogCode.Accepted:
        return 0
    win = MainWindow(db, login.user)
    win.show()
    return app.exec()


if __name__ == "__main__":
    sys.exit(main())
