"""
Sari-Sari Store Inventory, Sales & Profit System  (Python + Flask)

Built from our lessons:
    ARRAY        -> Python lists (traverse, search, find lowest, sort)
    STACK ADT    -> undo history              (push, pop, peek, size, isEmpty, isFull)
    LIST ADT     -> linked list of products   (get, insert, remove, removeAt, replace, size, isEmpty, isFull)
    QUEUE ADT    -> restock queue (FIFO)      (enqueue, dequeue, peek, size, isEmpty)

WHERE EACH DSA CONCEPT IS USED  (search for "DSA:" to find every comment)
    LIST ADT  (linked list)  -> Store.products ........ every product is a Node in the list
    STACK ADT (LIFO)         -> Store.history ......... every action is pushed; Undo pops the top
    QUEUE ADT (FIFO)         -> Store.restock ......... low-stock items wait in line to be restocked
    ARRAY                    -> Store.sales, search results, sorting, reports (traverse / search / sort)

Run:
    pip install flask
    python app.py
Open http://127.0.0.1:5000
"""
import json
import os
import random
import re
import tempfile
import threading
from datetime import date, datetime, timedelta

from flask import Flask, flash, redirect, render_template, request, session, url_for
from jinja2 import DictLoader
from werkzeug.security import check_password_hash, generate_password_hash

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
USERS_FILE = os.path.join(DATA_DIR, "users.json")

LOW_STOCK = 5            # stock at or below this is "low"
MAX_QTY = 100_000
MAX_PRICE = 100_000
MAX_PRODUCTS = 500       # DSA: capacity of the product linked list  -> used by isFull()
MAX_HISTORY = 200        # DSA: capacity of the undo stack           -> used by isFull()
NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9 .,'&()/-]{0,39}$")
USER_RE = re.compile(r"^[a-z0-9_]{3,20}$")


class ValidationError(Exception):
    """Raised when user input or an action is not allowed."""


# ======================================================================
#  DATA CLASSES
# ======================================================================
class Product:
    def __init__(self, name, qty, cost, price):
        self.name = name
        self.qty = qty
        self.cost = cost      # capital (cost) price
        self.price = price    # selling price

    def isLow(self):
        return self.qty <= LOW_STOCK

    def toDict(self):
        return {"name": self.name, "qty": self.qty, "cost": self.cost, "price": self.price}

    @classmethod
    def fromDict(cls, d):
        return cls(str(d["name"]), int(d["qty"]), float(d["cost"]), float(d["price"]))


# ======================================================================
#  DSA: LIST ADT  (Linked List: node = data + pointer to next)
#     [A|*] -> [B|*] -> [C|NULL]
#  Used for: Store.products  (the product list)
# ======================================================================
class Node:
    # DSA: a NODE has two parts -> the data (a Product) and a pointer to the next node
    def __init__(self, data):
        self.data = data
        self.next = None      # None = NULL (end of the list)


class LinkedList:
    def __init__(self, capacity=MAX_PRODUCTS):
        self.head = None      # DSA: HEAD = pointer to the first node
        self.count = 0
        self.capacity = capacity

    def isEmpty(self):
        # DSA: List ADT -> isEmpty()
        return self.count == 0

    def isFull(self):
        # DSA: List ADT -> isFull()  (we limit the list to MAX_PRODUCTS)
        return self.count >= self.capacity

    def size(self):
        # DSA: List ADT -> size()
        return self.count

    def get(self, position):
        # DSA: List ADT -> get(position)
        # start at head, move forward "position" times, return that node's data
        if position < 0 or position >= self.count:
            return None
        cur = self.head
        for _ in range(position):
            cur = cur.next
        return cur.data

    def insert(self, position, value):
        # DSA: List ADT -> insert(position, value)
        # make new node, point new node to the next node, point previous node to the new node
        if self.isFull():
            raise ValidationError("The list is full.")
        if position < 0 or position > self.count:
            position = self.count
        node = Node(value)
        if position == 0:
            node.next = self.head          # new node points to the old first node
            self.head = node               # head now points to the new node
        else:
            prev = self.head
            for _ in range(position - 1):  # walk to the node BEFORE the position
                prev = prev.next
            node.next = prev.next          # new node -> next node
            prev.next = node               # previous node -> new node
        self.count += 1

    def removeAt(self, position):
        # DSA: List ADT -> removeAt(position)
        # find the node before it, then link previous -> next (skip over the node)
        if position < 0 or position >= self.count:
            return None
        if position == 0:
            removed = self.head
            self.head = removed.next
        else:
            prev = self.head
            for _ in range(position - 1):
                prev = prev.next
            removed = prev.next
            prev.next = removed.next       # skip the removed node
        self.count -= 1
        return removed.data

    def remove(self, value):
        # DSA: List ADT -> remove(value)
        # remove the first node whose data equals value
        pos = 0
        cur = self.head
        while cur:
            if cur.data == value:
                return self.removeAt(pos)
            cur = cur.next
            pos += 1
        return None

    def replace(self, position, newValue):
        # DSA: List ADT -> replace(position, newValue)
        # find node at position, set its data = newValue (links stay the same)
        if position < 0 or position >= self.count:
            return False
        cur = self.head
        for _ in range(position):
            cur = cur.next
        cur.data = newValue
        return True

    def toArray(self):
        # DSA: TRAVERSE the linked list from head to NULL, copying each item into an ARRAY
        items = []
        cur = self.head
        while cur:
            items.append(cur.data)
            cur = cur.next
        return items

    def __iter__(self):
        # lets us write: for p in self.products   (a traversal)
        return iter(self.toArray())

    def __len__(self):
        return self.count


# ======================================================================
#  DSA: STACK ADT  (LIFO: Last In, First Out) -- only the TOP is touched
#  Used for: Store.history  (UNDO)
# ======================================================================
class Stack:
    def __init__(self, items=None, capacity=MAX_HISTORY):
        self.items = list(items or [])    # the end of the array is the TOP of the stack
        self.capacity = capacity

    def push(self, value):
        # DSA: Stack ADT -> push(value): add value to the top
        if self.isFull():
            raise ValidationError("Stack is full.")
        self.items.append(value)

    def pop(self):
        # DSA: Stack ADT -> pop(): take the top value, remove it, return it
        if self.isEmpty():
            return None
        return self.items.pop()

    def peek(self):
        # DSA: Stack ADT -> peek(): look at the top value WITHOUT removing it
        if self.isEmpty():
            return None
        return self.items[-1]

    def size(self):
        # DSA: Stack ADT -> size()
        return len(self.items)

    def isEmpty(self):
        # DSA: Stack ADT -> isEmpty()
        return len(self.items) == 0

    def isFull(self):
        # DSA: Stack ADT -> isFull()
        return len(self.items) >= self.capacity

    def toArray(self):
        return list(self.items)


# ======================================================================
#  DSA: QUEUE ADT  (FIFO: First In, First Out)
#       add at the REAR (enqueue), remove from the FRONT (dequeue)
#  Used for: Store.restock  (low-stock items waiting to be restocked)
# ======================================================================
class Queue:
    def __init__(self, items=None):
        self.items = list(items or [])    # index 0 = FRONT, last index = REAR

    def enqueue(self, value):
        # DSA: Queue ADT -> enqueue(value): add value to the back (rear)
        self.items.append(value)

    def dequeue(self):
        # DSA: Queue ADT -> dequeue(): remove and return the front value
        if self.isEmpty():
            return None
        return self.items.pop(0)

    def peek(self):
        # DSA: Queue ADT -> peek(): look at the front value without removing it
        if self.isEmpty():
            return None
        return self.items[0]

    def size(self):
        # DSA: Queue ADT -> size()
        return len(self.items)

    def isEmpty(self):
        # DSA: Queue ADT -> isEmpty()
        return len(self.items) == 0

    def contains(self, value):
        # DSA: ARRAY SEARCH (traverse) -> is the value already in the queue?
        for item in self.items:
            if item == value:
                return True
        return False

    def toArray(self):
        return list(self.items)


# ======================================================================
#  DSA: ARRAY ALGORITHMS  (traverse, find lowest, sort, search)
# ======================================================================
def findLowest(items, key):
    # DSA: ARRAY -> Find the Lowest Value
    #   min = array[0]; for each item: if item < min: min = item
    if len(items) == 0:
        return None
    lowest = items[0]
    for item in items:
        if key(item) < key(lowest):
            lowest = item
    return lowest


def selectionSort(items, key):
    # DSA: ARRAY -> SORT (selection sort)
    #   for each position i, find the smallest item from i to the end and swap it into i
    arr = list(items)
    for i in range(len(arr) - 1):
        smallest = i
        for j in range(i + 1, len(arr)):
            if key(arr[j]) < key(arr[smallest]):
                smallest = j
        arr[i], arr[smallest] = arr[smallest], arr[i]
    return arr


def matchesKeyword(name, words):
    # every keyword must appear somewhere in the name ("coke" -> all Coke products)
    lowered = name.lower()
    for w in words:
        if w not in lowered:
            return False
    return True


def searchProducts(products, query):
    # DSA: ARRAY -> SEARCH (linear search)
    #   for each item in array: if it matches, add it to the results
    words = query.lower().split()
    results = []
    if len(words) == 0:
        return results
    for p in products:                   # traverse every product, one by one
        if matchesKeyword(p.name, words):
            results.append(p)
    return results


# ======================================================================
#  INPUT CHECKING
# ======================================================================
def cleanName(raw, label="Product name"):
    name = " ".join((raw or "").split())
    if not name:
        raise ValidationError(f"{label} is required.")
    if not NAME_RE.match(name):
        raise ValidationError(f"{label} has invalid characters or is too long (max 40).")
    return name


def parseInt(raw, label, minimum=1, maximum=MAX_QTY):
    try:
        value = int(str(raw).strip())
    except (ValueError, TypeError):
        raise ValidationError(f"{label} must be a whole number.")
    if value < minimum or value > maximum:
        raise ValidationError(f"{label} must be between {minimum} and {maximum:,}.")
    return value


def parseMoney(raw, label):
    try:
        value = float(str(raw).strip().replace(",", ""))
    except (ValueError, TypeError):
        raise ValidationError(f"{label} must be a number.")
    if value != value or value <= 0 or value > MAX_PRICE:
        raise ValidationError(f"{label} must be more than 0 and not above {MAX_PRICE:,}.")
    return round(value, 2)


def parseDate(raw, label="Date"):
    try:
        return datetime.strptime((raw or "").strip(), "%Y-%m-%d").date()
    except ValueError:
        raise ValidationError(f"{label} must be in YYYY-MM-DD format.")


# ======================================================================
#  SAMPLE DATA (demo account only):  name|cost|price|stock|popularity
# ======================================================================
_SAMPLE_TEXT = """
Coke Mismo 295ml|14|18|24|7
Coke Zero 330ml|19|24|10|2
Coke 500ml|26|32|14|3
Coke 1.5L|58|68|8|2
Sprite Mismo 295ml|14|18|18|5
Sprite 500ml|26|32|10|2
Royal Mismo 295ml|14|18|15|5
Royal 500ml|26|32|9|2
C2 Green Tea 230ml|17|20|12|4
Mineral Water 500ml|8|12|30|6
Zest-O Orange 200ml|9|12|20|4
Great Taste White 3-in-1|6|8|60|8
Nescafe Original 3-in-1|6.5|8|55|7
Kopiko Brown Coffee|6|8|48|7
Milo Sachet 24g|6.5|8|36|5
Bear Brand Sachet 33g|11|13|22|4
Energen Chocolate|7|9|25|4
Tang Orange Sachet|5.5|7|4|3
Lucky Me Pancit Canton Original|13|16|40|9
Lucky Me Pancit Canton Kalamansi|13|16|26|5
Lucky Me Chicken Mami 55g|9.5|12|32|6
Payless Pancit Canton|11.5|14|18|4
Nissin Cup Noodles Seafood|28|35|10|2
Piattos Cheese 40g|14|17|20|5
Chippy Barbecue 27g|8|10|30|6
Oishi Prawn Crackers 60g|12|15|14|3
Mang Juan Chicharon|8|10|3|3
Skyflakes Crackers Single|6.5|8|34|6
Choc-Nut Chocolate|0.9|1.5|120|6
Maxx Menthol Candy|0.8|1|200|8
Clover Chips Cheese 24g|8|10|0|3
Silver Swan Soy Sauce 200ml|14|17|14|3
Silver Swan Soy Sauce 385ml|22|27|9|2
Silver Swan Vinegar 200ml|10|13|11|2
Datu Puti Vinegar 200ml|11|14|13|3
Datu Puti Vinegar 385ml|17|21|9|2
Datu Puti Patis 200ml|16|20|9|2
Magic Sarap 8g|3.2|4|80|8
Ajinomoto 50g|8|10|40|4
Iodized Salt 500g|14|18|11|2
Ligo Sardines 155g|19|23|20|4
555 Tuna Afritada 155g|26|32|15|3
Argentina Corned Beef 150g|36|42|12|2
Egg (per piece)|8.5|10|60|9
Rice (per kilo)|48|55|40|4
White Sugar (per kilo)|62|70|12|2
Cooking Oil 100ml|16|20|14|3
Palmolive Shampoo Sachet|5.5|7|60|6
Sunsilk Shampoo Sachet|5.5|7|52|6
Safeguard Soap 55g|22|27|10|2
Colgate Toothpaste Sachet|5.5|7|18|3
Matches (box)|2|3|40|3
Biogesic 500mg (tablet)|3|4|30|3
"""
SAMPLE_PRODUCTS = []
for _line in _SAMPLE_TEXT.strip().splitlines():
    _n, _c, _p, _s, _w = _line.split("|")
    SAMPLE_PRODUCTS.append((_n, float(_c), float(_p), int(_s), int(_w)))


# ======================================================================
#  USER ACCOUNTS (saved in data/users.json, passwords are hashed)
# ======================================================================
def writeJson(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), suffix=".tmp")
    with os.fdopen(fd, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
    os.replace(tmp, path)


def loadUsers():
    try:
        with open(USERS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except (OSError, ValueError):
        return {}


# ======================================================================
#  STORE  (one per account) -- this is where the 3 ADTs + array work together
# ======================================================================
class Store:
    def __init__(self, username):
        self.username = username
        self.path = os.path.join(DATA_DIR, f"{username}.json")
        self.reset()

    def reset(self):
        self.products = LinkedList()     # DSA: LIST ADT   -> all products (nodes)
        self.sales = []                  # DSA: ARRAY      -> every sale record, in order (index 0, 1, 2 ...)
        self.capital = 0.0               # total money spent buying stock
        self.history = Stack()           # DSA: STACK ADT  -> undo history (LIFO)
        self.restock = Queue()           # DSA: QUEUE ADT  -> low-stock items (FIFO)

    # ---------- saving / loading ----------
    def save(self):
        data = {
            "products": [p.toDict() for p in self.products],   # DSA: traverse the linked list
            "sales": self.sales,
            "capital": round(self.capital, 2),
            "history": self.history.toArray(),
            "restock": self.restock.toArray(),
        }
        writeJson(self.path, data)

    def load(self):
        if not os.path.exists(self.path):
            return
        try:
            with open(self.path, encoding="utf-8") as f:
                data = json.load(f)
            self.reset()
            for d in data.get("products", []):
                # DSA: List ADT -> insert at the END (position = size) to keep the saved order
                self.products.insert(self.products.size(), Product.fromDict(d))
            self.sales = list(data.get("sales", []))
            self.capital = float(data.get("capital", 0))
            self.history = Stack(data.get("history", []))
            self.restock = Queue(data.get("restock", []))
        except Exception:
            self.reset()          # damaged file -> start clean instead of crashing

    def loadSample(self, days=30):
        self.reset()
        rng = random.Random(2026)
        today = date.today()
        weights = [item[4] for item in SAMPLE_PRODUCTS]
        sold = {item[0]: 0 for item in SAMPLE_PRODUCTS}
        for offset in range(days - 1, -1, -1):
            day = today - timedelta(days=offset)
            for _ in range(rng.randint(10, 18)):
                name, cost, price, _s, _w = rng.choices(SAMPLE_PRODUCTS, weights=weights)[0]
                qty = rng.randint(1, 3)
                revenue, cogs = round(qty * price, 2), round(qty * cost, 2)
                # DSA: ARRAY -> append each sale to the end of the sales array
                self.sales.append({"date": day.isoformat(), "name": name, "qty": qty,
                                   "price": price, "cost": cost, "revenue": revenue,
                                   "cogs": cogs, "profit": round(revenue - cogs, 2)})
                sold[name] += qty
        for name, cost, price, stock, _w in SAMPLE_PRODUCTS:
            # DSA: List ADT -> insert each product at the end of the linked list
            self.products.insert(self.products.size(), Product(name, stock, cost, price))
            self.capital += (stock + sold[name]) * cost
        self.changed()

    # ---------- helpers ----------
    def indexOf(self, name):
        # DSA: SEARCH (linear) on the linked list:
        #      traverse node by node, return the POSITION of the match (or -1 if not found)
        key = (name or "").strip().lower()
        position = 0
        for p in self.products:
            if p.name.lower() == key:
                return position
            position += 1
        return -1

    def need(self, name):
        position = self.indexOf(name)                  # DSA: search -> get the position
        if position == -1:
            raise ValidationError(f"Product '{name}' was not found.")
        return self.products.get(position)             # DSA: List ADT -> get(position)

    def syncQueue(self):
        # DSA: QUEUE ADT keeps the restock line up to date
        # Step 1: take every name out of the FRONT (dequeue). If the product still exists
        #         and is still low, put it back at the REAR (enqueue). Order stays the same.
        for _ in range(self.restock.size()):
            name = self.restock.dequeue()
            position = self.indexOf(name)
            if position != -1 and self.products.get(position).isLow():
                self.restock.enqueue(name)
        # Step 2: traverse the product list; newly-low products join the REAR of the queue
        for p in self.products:
            if p.isLow() and not self.restock.contains(p.name):
                self.restock.enqueue(p.name)

    def changed(self):
        self.capital = round(self.capital, 2)
        self.syncQueue()      # DSA: queue refreshed after every change
        self.save()

    def pushHistory(self, entry):
        # DSA: STACK ADT -> push(entry). If the stack isFull(), drop the oldest (bottom) first.
        if self.history.isFull():
            self.history = Stack(self.history.toArray()[1:])
        self.history.push(entry)

    # ---------- features ----------
    def addProduct(self, name, qty, cost, price):
        if self.indexOf(name) != -1:                   # DSA: search -> no duplicates
            raise ValidationError(f"'{name}' already exists. Use Add Stock instead.")
        if self.products.isFull():                     # DSA: List ADT -> isFull()
            raise ValidationError(f"You can only keep {MAX_PRODUCTS} products.")
        # DSA: List ADT -> insert(size, value) = add a new node at the end
        self.products.insert(self.products.size(), Product(name, qty, cost, price))
        spent = round(qty * cost, 2)
        self.capital += spent
        # DSA: Stack ADT -> push(): remember what happened so Undo can reverse it
        self.pushHistory({"type": "add_product", "name": name, "spent": spent,
                          "label": f"Added product {name}"})
        self.changed()

    def addStock(self, name, qty, cost):
        p = self.need(name)
        if p.qty + qty > MAX_QTY:
            raise ValidationError(f"Stock cannot go above {MAX_QTY:,}.")
        spent = round(qty * cost, 2)
        # DSA: Stack ADT -> push() BEFORE changing, saving the old cost so Undo can restore it
        self.pushHistory({"type": "add_stock", "name": p.name, "qty": qty, "spent": spent,
                          "old_cost": p.cost, "label": f"Added {qty} stock to {p.name}"})
        p.cost = round(cost if p.qty == 0 else (p.qty * p.cost + qty * cost) / (p.qty + qty), 2)
        p.qty += qty
        self.capital += spent
        self.changed()

    def updatePrice(self, name, cost, price):
        p = self.need(name)
        # DSA: Stack ADT -> push() the OLD prices so Undo can put them back
        self.pushHistory({"type": "price", "name": p.name, "old_cost": p.cost,
                          "old_price": p.price, "label": f"Changed price of {p.name}"})
        p.cost, p.price = cost, price
        self.changed()

    def removeProduct(self, name):
        position = self.indexOf(name)                  # DSA: search -> find the position
        if position == -1:
            raise ValidationError(f"Product '{name}' was not found.")
        # DSA: List ADT -> removeAt(position): link previous node to next node (skip it)
        removed = self.products.removeAt(position)
        # DSA: Stack ADT -> push() the product AND its position, so Undo can insert it back
        self.pushHistory({"type": "remove", "product": removed.toDict(), "position": position,
                          "label": f"Removed product {removed.name}"})
        self.changed()

    def recordSale(self, name, qty, when):
        p = self.need(name)
        if when > date.today():
            raise ValidationError("Sale date cannot be in the future.")
        if qty > p.qty:
            raise ValidationError(f"Not enough stock. Only {p.qty} left.")
        p.qty -= qty                                   # stock updates automatically
        revenue = round(qty * p.price, 2)
        cogs = round(qty * p.cost, 2)
        sale = {"date": when.isoformat(), "name": p.name, "qty": qty, "price": p.price,
                "cost": p.cost, "revenue": revenue, "cogs": cogs,
                "profit": round(revenue - cogs, 2)}
        self.sales.append(sale)                        # DSA: ARRAY -> add the sale at the end
        self.pushHistory({"type": "sale", "sale": sale, "label": f"Sold {qty} x {p.name}"})  # DSA: push
        self.changed()

    def restockNext(self, qty, cost):
        self.syncQueue()
        if self.restock.isEmpty():                     # DSA: Queue ADT -> isEmpty()
            raise ValidationError("Nothing needs restocking.")
        name = self.restock.peek()                     # DSA: Queue ADT -> peek() = FRONT of the line (FIFO)
        # Restocking removes the item from the low list, so changed() -> syncQueue() dequeues it.
        self.addStock(name, qty, cost)                 # may raise -> item stays in the queue
        return name

    def undo(self):
        # DSA: STACK ADT (LIFO) -> the LAST action done is the FIRST one undone
        last = self.history.peek()                     # look at the TOP without removing it
        if last is None:
            raise ValidationError("Nothing to undo.")
        kind = last["type"]
        if kind == "sale":
            sale = last["sale"]
            position = self.indexOf(sale["name"])
            if position != -1:
                self.products.get(position).qty += sale["qty"]    # put the stock back
            if self.sales:
                self.sales.pop()                       # DSA: ARRAY -> remove the last sale record
        elif kind == "add_product":
            position = self.indexOf(last["name"])
            if position != -1:
                self.products.removeAt(position)       # DSA: List ADT -> removeAt
            self.capital -= last["spent"]
        elif kind == "add_stock":
            position = self.indexOf(last["name"])
            if position != -1:
                p = self.products.get(position)
                p.qty = max(0, p.qty - last["qty"])
                p.cost = last["old_cost"]
            self.capital -= last["spent"]
        elif kind == "price":
            position = self.indexOf(last["name"])
            if position != -1:
                p = self.products.get(position)
                p.cost, p.price = last["old_cost"], last["old_price"]
        elif kind == "remove":
            # DSA: List ADT -> insert(position, value): put the node back where it was
            self.products.insert(last["position"], Product.fromDict(last["product"]))
        self.history.pop()                             # DSA: Stack ADT -> pop(): remove the top
        self.changed()
        return f"Undone: {last.get('label', 'last action')}"


# ======================================================================
#  FLASK APP
# ======================================================================
app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "sari-sari-dev-key")
lock = threading.RLock()
stores = {}                  # username -> Store (kept in memory)
users = loadUsers()


def ensureDemo():
    if "demo" not in users:
        users["demo"] = {"hash": generate_password_hash("demo123"), "store": "Gina Store"}
        writeJson(USERS_FILE, users)
    if not os.path.exists(os.path.join(DATA_DIR, "demo.json")):
        demo = Store("demo")
        demo.loadSample()


def getStore():
    name = session.get("user")
    if name not in stores:
        s = Store(name)
        s.load()
        stores[name] = s
    return stores[name]


@app.template_filter("peso")
def peso(value):
    try:
        return f"₱{float(value):,.2f}"
    except (TypeError, ValueError):
        return "₱0.00"


@app.context_processor
def injectGlobals():
    info = {"user": session.get("user"), "store_name": "Gina Store",
            "low_stock": LOW_STOCK,
            "today": date.today().isoformat(), "undo_label": None, "restock_count": 0}
    if info["user"] in users:
        info["store_name"] = "Gina Store"
        s = getStore()
        last = s.history.peek()          # DSA: Stack ADT -> peek() tells the Undo button what it will undo
        info["undo_label"] = last.get("label", "last action") if last else None
        info["restock_count"] = s.restock.size()     # DSA: Queue ADT -> size() = number in the Low Stock menu
    return info


@app.before_request
def requireLogin():
    if request.endpoint in ("login", "signup", "static", None):
        return None
    if session.get("user") not in users:
        session.clear()
        return redirect(url_for("login"))
    return None


def attempt(action):
    """Run an action; show a friendly message instead of ever crashing."""
    try:
        with lock:
            flash(action(), "success")
    except ValidationError as err:
        flash(str(err), "error")
    except Exception:
        flash("Something went wrong. Please check your input and try again.", "error")


# ---------------- accounts ----------------
@app.route("/login", methods=["GET", "POST"])
def login():
    if session.get("user") in users:
        return redirect(url_for("inventory"))
    if request.method == "POST":
        name = (request.form.get("username") or "").strip().lower()
        password = request.form.get("password") or ""
        account = users.get(name)
        if account and check_password_hash(account["hash"], password):
            session.clear()
            session["user"] = name
            return redirect(url_for("inventory"))
        flash("Incorrect username or password.", "error")
    return render_template("login.html")


@app.route("/signup", methods=["GET", "POST"])
def signup():
    if request.method == "POST":
        name = (request.form.get("username") or "").strip().lower()
        password = request.form.get("password") or ""
        confirm = request.form.get("confirm") or ""
        error = None
        store_name = ""
        try:
            store_name = cleanName(request.form.get("store"), "Store name")
        except ValidationError as err:
            error = str(err)
        if error:
            pass
        elif not USER_RE.match(name):
            error = "Username must be 3-20 characters: letters, numbers or underscore."
        elif name in users:
            error = "That username is already taken."
        elif len(password) < 4 or len(password) > 64:
            error = "Password must be 4-64 characters."
        elif password != confirm:
            error = "Passwords do not match."
        if error:
            flash(error, "error")
        else:
            try:
                with lock:
                    users[name] = {"hash": generate_password_hash(password), "store": store_name}
                    writeJson(USERS_FILE, users)
                    store = Store(name)          # brand-new, empty store (empty list, stack, queue)
                    store.save()
                    stores[name] = store
                session.clear()
                session["user"] = name
                flash("Account created. Your store is empty, add your first product!", "success")
                return redirect(url_for("inventory"))
            except OSError:
                users.pop(name, None)
                flash("Could not save your account. Please try again.", "error")
    return render_template("signup.html")


@app.post("/logout")
def logout():
    session.clear()
    return redirect(url_for("login"))


# ---------------- inventory ----------------
@app.get("/")
def inventory():
    s = getStore()
    sort = request.args.get("sort", "added")
    items = s.products.toArray()          # DSA: traverse the linked list -> copy into an ARRAY
    if sort == "name":
        items = selectionSort(items, key=lambda p: p.name.lower())   # DSA: ARRAY sort (A to Z)
    elif sort == "stock":
        items = selectionSort(items, key=lambda p: p.qty)            # DSA: ARRAY sort (lowest stock first)
    else:
        sort = "added"
    stock_value = 0
    low_count = 0
    for p in items:                        # DSA: ARRAY traverse -> add up values and count low items
        stock_value += p.qty * p.cost
        if p.isLow():
            low_count += 1
    return render_template("inventory.html", items=items, sort=sort,
                           stock_value=stock_value, low_count=low_count)


@app.post("/add")
def addProduct():
    def action():
        getStore().addProduct(cleanName(request.form.get("name")),
                              parseInt(request.form.get("qty"), "Quantity", 0),
                              parseMoney(request.form.get("cost"), "Cost price"),
                              parseMoney(request.form.get("price"), "Selling price"))
        return "Product added."
    attempt(action)
    return redirect(url_for("inventory"))


@app.post("/stock")
def addStock():
    def action():
        getStore().addStock(request.form.get("name"),
                            parseInt(request.form.get("qty"), "Quantity"),
                            parseMoney(request.form.get("cost"), "Cost price"))
        return "Stock added."
    attempt(action)
    return redirect(url_for("inventory"))


@app.post("/price")
def updatePrice():
    def action():
        getStore().updatePrice(request.form.get("name"),
                               parseMoney(request.form.get("cost"), "Cost price"),
                               parseMoney(request.form.get("price"), "Selling price"))
        return "Prices updated."
    attempt(action)
    return redirect(url_for("inventory"))


@app.post("/remove")
def removeProduct():
    def action():
        getStore().removeProduct(request.form.get("name"))
        return "Product removed."
    attempt(action)
    return redirect(url_for("inventory"))


# ---------------- sales ----------------
@app.route("/sales", methods=["GET", "POST"])
def sales():
    s = getStore()
    if request.method == "POST":
        def action():
            s.recordSale(request.form.get("name"),
                         parseInt(request.form.get("qty"), "Quantity"),
                         parseDate(request.form.get("date")))
            return "Sale recorded. Stock and reports updated."
        attempt(action)
        return redirect(url_for("sales"))
    available = [p for p in s.products if p.qty > 0]    # DSA: traverse the list, keep items with stock
    recent = list(reversed(s.sales[-10:]))              # DSA: ARRAY -> last 10 sales, newest first
    return render_template("sales.html", products=available, recent=recent)


# ---------------- reports ----------------
@app.get("/reports")
def reports():
    s = getStore()
    today = date.today()
    try:
        day = parseDate(request.args.get("day", today.isoformat())).isoformat()
    except ValidationError:
        day = today.isoformat()
    month = request.args.get("month", day[:7])
    if not re.match(r"^\d{4}-(0[1-9]|1[0-2])$", month):
        month = day[:7]

    overall = {"capital": s.capital, "revenue": 0, "profit": 0, "stock_value": 0}
    d = {"revenue": 0, "profit": 0, "items": 0}
    m = {"revenue": 0, "profit": 0, "items": 0}
    by_day, by_month = {}, {}
    # DSA: ARRAY -> TRAVERSE the sales array once, adding up totals for the
    #      overall, daily and monthly reports (total sales, profit, items sold)
    for sale in s.sales:
        overall["revenue"] += sale["revenue"]
        overall["profit"] += sale["profit"]
        if sale["date"] == day:
            d["revenue"] += sale["revenue"]; d["profit"] += sale["profit"]; d["items"] += sale["qty"]
        if sale["date"][:7] == month:
            m["revenue"] += sale["revenue"]; m["profit"] += sale["profit"]; m["items"] += sale["qty"]
            row = by_day.setdefault(sale["date"], {"revenue": 0, "profit": 0, "items": 0})
            row["revenue"] += sale["revenue"]; row["profit"] += sale["profit"]; row["items"] += sale["qty"]
        row = by_month.setdefault(sale["date"][:7], {"revenue": 0, "profit": 0, "items": 0})
        row["revenue"] += sale["revenue"]; row["profit"] += sale["profit"]; row["items"] += sale["qty"]
    for p in s.products:                   # DSA: traverse the linked list -> stock value
        overall["stock_value"] += p.qty * p.cost
    days = [(k, by_day[k]) for k in sorted(by_day, reverse=True)]
    months = [(k, by_month[k]) for k in sorted(by_month, reverse=True)]
    return render_template("reports.html", day=day, month=month, d=d, m=m, overall=overall,
                           days=days, months=months)


# ---------------- search ----------------
@app.get("/search")
def search():
    q = " ".join(request.args.get("q", "").split())[:60]
    # DSA: ARRAY linear search over the product list (keyword match, e.g. "coke")
    found = searchProducts(getStore().products, q) if q else None
    return render_template("search.html", q=q, found=found)


# ---------------- restock (low stock + queue) ----------------
@app.route("/restock", methods=["GET", "POST"])
def restock():
    s = getStore()
    if request.method == "POST":
        def action():
            name = s.restockNext(parseInt(request.form.get("qty"), "Quantity"),
                                 parseMoney(request.form.get("cost"), "Cost price"))
            return f"Restocked {name}."
        attempt(action)
        return redirect(url_for("restock"))
    s.syncQueue()
    items = []
    # DSA: Queue ADT -> read the line from FRONT to REAR, then search the list for each product
    for name in s.restock.toArray():
        position = s.indexOf(name)
        if position != -1:
            items.append(s.products.get(position))
    return render_template("restock.html", items=items)


# ---------------- undo / history ----------------
@app.post("/undo")
def undo():
    # DSA: Stack ADT -> Store.undo() peeks the TOP, reverses it, then pops it
    attempt(lambda: getStore().undo())
    return redirect(request.referrer or url_for("inventory"))


@app.get("/history")
def history():
    # DSA: Stack ADT -> show the stack TOP first (reversed), so the next Undo is at the top
    entries = [e.get("label", "Action") for e in reversed(getStore().history.toArray())]
    return render_template("history.html", entries=entries)


# ---------------- friendly errors (no raw "Internal Server Error") ----------------
@app.errorhandler(404)
def notFound(_e):
    return render_template("error.html", title="Page not found",
                           text="That page does not exist."), 404


@app.errorhandler(Exception)
def anyError(e):
    code = getattr(e, "code", 500)
    if not isinstance(code, int):
        code = 500
    if code == 405:
        return render_template("error.html", title="Not allowed",
                               text="That action is not allowed here."), 405
    if code < 500 and code != 500 and hasattr(e, "code"):
        return render_template("error.html", title="Request problem",
                               text="Please go back and try again."), code
    return render_template("error.html", title="Something went wrong",
                           text="Your data is safe. Please go back and try again."), 500


# ======================================================================
#  TEMPLATES
# ======================================================================
TEMPLATES = {
# ---------- reusable pieces (macros): written once, used on every page ----------
"macros.html": """{% macro attrs(d) %}{% for k, v in d.items() %} {{ k }}{% if v is not sameas true %}="{{ v }}"{% endif %}{% endfor %}{% endmacro %}
{% macro field(label, name, type='text', box='', id='') %}<div{% if box %} style="{{ box }}"{% endif %}><label{% if id %} for="{{ id }}"{% endif %}>{{ label }}</label><input name="{{ name }}" type="{{ type }}"{% if id %} id="{{ id }}"{% endif %}{{ attrs(kwargs) }}></div>{% endmacro %}
{% macro pw(label, name, id, auto) %}<label for="{{ id }}">{{ label }}</label><div class="pw"><input name="{{ name }}" type="password" id="{{ id }}" required autocomplete="{{ auto }}"{{ attrs(kwargs) }}><button type="button" class="toggle" onclick="togglePwd('{{ id }}', this)">Show</button></div>{% endmacro %}
{% macro stat(label, value, cls='') %}<div class="stat {{ cls }}"><span>{{ label }}</span><b>{{ value }}</b></div>{% endmacro %}
{% macro card(title='', style='') %}<div class="card"{% if style %} style="{{ style }}"{% endif %}>{% if title %}<h3>{{ title }}</h3>{% endif %}{{ caller() }}</div>{% endmacro %}
{% macro report_table(first, rows, link=false) %}<div class="scroll"><table>
<tr><th>{{ first }}</th><th>Items</th><th>Sales</th><th>Profit</th></tr>
{% for k, v in rows %}<tr><td>{% if link %}<a href="{{ url_for('reports', month=k) }}">{{ k }}</a>{% else %}{{ k }}{% endif %}</td><td>{{ v['items'] }}</td><td>{{ v.revenue|peso }}</td><td>{{ v.profit|peso }}</td></tr>
{% else %}<tr><td colspan="4" class="muted">No sales{{ ' yet' if link else ' this month' }}.</td></tr>{% endfor %}
</table></div>{% endmacro %}""",
 
"base.html": """<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{{ store_name }}</title>
<link href="https://fonts.googleapis.com/css2?family=Cormorant+Garamond:wght@500;600;700&family=Inter:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--forest:#c6537d;--forest-d:#a83d67;--gold:#e6a0b8;--gold-d:#b84f78;--ivory:#fff4f8;--paper:#fffafd;--ink:#3b2931;--muted:#806d75;--rule:#f0d6e0;--field:#dfbdcb;--wine:#a83d67;
--serif:'Cormorant Garamond','Playfair Display',Georgia,'Times New Roman',serif;--sans:'Inter','DM Sans',system-ui,-apple-system,'Segoe UI',sans-serif;
--shadow:0 1px 2px rgba(198,83,125,.06),0 10px 28px rgba(198,83,125,.07)}
*{box-sizing:border-box}
html{-webkit-text-size-adjust:100%}
body{margin:0;font:15px/1.55 var(--sans);color:var(--ink);background:var(--ivory);-webkit-font-smoothing:antialiased}
a{color:var(--forest)}
.muted{color:var(--muted)}
.inline{display:inline}
.scroll{overflow-x:auto}
 
/* header and menu */
header{background:var(--forest);color:#fff;border-bottom:3px solid var(--gold)}
header h1{margin:0;color:var(--ivory);font-family:var(--serif);font-weight:600;letter-spacing:.04em}
body.auth header{padding:.8rem 3.6rem}
body.auth header h1{font-size:1.9rem;line-height:1.3}
body.app header{padding:1.1rem 1.5rem .5rem}
body.app header h1{text-align:center;font-size:2.4rem;line-height:1.25}
nav{display:flex;flex-wrap:wrap;align-items:center;gap:.6rem 1rem;margin-top:.9rem;padding-top:.4rem;border-top:1px solid rgba(255,255,255,.16)}
nav .links{display:flex;flex:1;flex-wrap:wrap;justify-content:space-around;gap:.2rem 1rem;min-width:0}
nav .links a{color:rgba(255,255,255,.78);text-decoration:none;font:500 .72rem var(--sans);letter-spacing:.18em;text-transform:uppercase;padding:.85rem .2rem;border-bottom:2px solid transparent;margin-bottom:-3px;transition:color .15s,border-color .15s}
nav .links a:hover{color:#fff}
nav .links a.on{color:#fff;border-bottom-color:var(--gold)}
nav .sp{display:flex;gap:.6rem;align-items:center}
nav .sp button{background:transparent;color:#fff;border:1px solid rgba(255,255,255,.45);padding:.45rem 1.05rem;font:500 .66rem var(--sans);letter-spacing:.16em}
nav .sp button:hover{background:#fff;color:var(--forest)}
nav .sp button:disabled{opacity:.4;background:transparent;color:#fff}
 
/* page, cards, stats */
main{max-width:1100px;margin:0 auto;padding:0 1.4rem 3.5rem}
body.auth main{max-width:640px}
.page-title{margin:2.2rem 0 2rem;text-align:center;font:500 2rem/1.2 var(--serif);letter-spacing:.2em;text-transform:uppercase;color:var(--forest)}
.page-title::after,.auth-title::after{content:"";display:block;width:56px;height:1px;background:var(--gold);margin:.9rem auto 0}
.card{background:var(--paper);border:1px solid var(--rule);border-radius:3px;padding:1.3rem 1.5rem 1.5rem;margin-bottom:1.6rem;box-shadow:var(--shadow)}
.narrow{max-width:460px;margin:3rem auto}
h3{margin:0 0 1.1rem;padding-bottom:.75rem;border-bottom:1px solid var(--rule);font:600 .7rem var(--sans);letter-spacing:.22em;text-transform:uppercase;color:var(--gold-d)}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(220px,1fr));gap:1.2rem;margin-bottom:1.8rem}
.card .grid{margin-bottom:1rem}
.grid.four{grid-template-columns:repeat(4,1fr)}
.stat{background:var(--paper);border:1px solid var(--rule);border-top:2px solid var(--gold);border-radius:3px;padding:1rem 1.25rem 1.05rem;box-shadow:var(--shadow)}
.stat span{display:block;font:600 .66rem var(--sans);letter-spacing:.2em;text-transform:uppercase;color:var(--muted)}
.stat b{display:block;margin-top:.15rem;font:600 2.1rem/1.25 var(--serif);letter-spacing:.01em;color:var(--forest);font-variant-numeric:lining-nums}
.stat.outline{box-shadow:none;background:#faf8f3;border-top:1px solid var(--rule)}
.stat.outline b{font-size:1.7rem}
.peso{display:inline-block;width:.58em;height:.76em;margin-right:.2em;vertical-align:baseline;overflow:visible}
 
/* tables */
table{width:100%;border-collapse:collapse}
th{font:600 .64rem var(--sans);letter-spacing:.18em;text-transform:uppercase;color:var(--muted);text-align:left;padding:.4rem .7rem .7rem;border-bottom:1px solid var(--ink)}
td{padding:1rem .7rem;border-bottom:1px solid var(--rule);vertical-align:top;font:400 .92rem var(--sans);font-variant-numeric:tabular-nums}
td:first-child{font:600 1.12rem var(--serif);color:var(--forest)}
tr:last-child td{border-bottom:0}
tr:hover>td{background:#faf8f3}
tr.low td{background:#fbf6ea}
.badge{background:#f6ecd7;color:#7a5a1c;border:1px solid #e6d3a8;border-radius:2px;padding:.05rem .5rem;margin-left:.4rem;font:600 .58rem var(--sans);letter-spacing:.14em;text-transform:uppercase;vertical-align:middle}
 
/* forms and buttons */
label{display:block;font:600 .64rem var(--sans);letter-spacing:.18em;text-transform:uppercase;color:var(--muted);margin:0 0 .4rem}
input,select{width:100%;height:2.7rem;padding:0 .85rem;border:1px solid var(--field);border-radius:3px;background:#fff;font:400 .9rem var(--sans);color:var(--ink);transition:border-color .15s,box-shadow .15s}
input:focus,select:focus{outline:0;border-color:var(--forest);box-shadow:0 0 0 3px rgba(198,83,125,.12)}
input[type=date],input[type=month]{width:210px}
button{background:var(--forest);color:#fff;border:1px solid var(--forest);border-radius:3px;padding:.72rem 1.6rem;font:600 .68rem var(--sans);letter-spacing:.18em;text-transform:uppercase;cursor:pointer;transition:background .15s,color .15s,border-color .15s}
button:hover{background:var(--forest-d);border-color:var(--forest-d)}
button:disabled{opacity:.5;cursor:not-allowed}
button.alt{background:transparent;color:var(--forest);padding:.72rem 1.8rem}
button.alt:hover{background:var(--forest);color:#fff}
button.danger{background:transparent;color:var(--wine);border-color:var(--wine);margin-top:.35rem}
button.danger:hover{background:var(--wine);color:#fff}
button.sm{padding:.4rem 1rem;font-size:.62rem}
.row{display:flex;flex-wrap:wrap;gap:1rem 1.4rem;align-items:flex-end}
.row>div{min-width:0}
details{margin-bottom:.25rem}
summary{cursor:pointer;font:500 .8rem var(--sans);color:var(--forest);letter-spacing:.02em}
summary::marker{color:var(--gold)}
details .row{margin-top:.5rem;gap:.5rem}
details input{width:90px;height:2.1rem;font-size:.8rem}
.sortline{margin:0 0 1rem;font:400 .78rem var(--sans);color:var(--muted)}
.sortline a{color:var(--ink);text-decoration:none;margin:0 .3rem}
.sortline a:hover{color:var(--forest)}
.sortline a.on{color:var(--forest);font-weight:600;text-decoration:underline;text-decoration-color:var(--gold);text-underline-offset:5px}
.note{margin:1.4rem 0 1rem;font:italic 400 .85rem var(--sans);color:var(--muted)}
.flash{padding:.75rem 1.1rem;border-radius:3px;margin:1.2rem 0 0;border:1px solid var(--rule);border-left:3px solid;font-size:.88rem;background:var(--paper);box-shadow:var(--shadow)}
.flash.error{color:var(--wine);border-left-color:var(--wine)}
.flash.success{color:var(--forest);border-left-color:var(--forest)}
ol.log{margin:0;padding-left:2.2rem;font:500 1.2rem var(--serif);line-height:2.1;color:var(--forest)}
ol.log li::marker{color:var(--gold);font-family:var(--sans);font-size:.85rem}
 
/* login and sign up */
.auth-title{margin:4rem 0 2rem;text-align:center;font:500 2.5rem/1.2 var(--serif);letter-spacing:.06em;color:var(--forest)}
.auth-title::after{margin-top:1rem}
.auth-box{width:min(320px,100%);margin:0 auto 3rem}
body.auth label{margin:1.1rem 0 .45rem}
body.auth input{height:3rem;padding:0 1rem}
.pw{position:relative}
.pw input{padding-right:4.5rem}
button.toggle{position:absolute;right:.9rem;top:50%;transform:translateY(-50%);background:none;border:0;color:var(--muted);padding:0;font:500 .62rem var(--sans);letter-spacing:.16em}
button.toggle:hover{background:none;color:var(--forest)}
.auth-note{margin:.7rem 0 0;text-align:right;font-size:.84rem;color:var(--muted)}
.auth-note a{font-weight:600;text-decoration:underline;text-decoration-color:var(--gold);text-underline-offset:3px}
body.auth button.submit{display:block;width:190px;height:2.9rem;margin:2rem auto 0;padding:0}
 
@media (max-width:900px){.grid.four{grid-template-columns:repeat(2,1fr)}}
@media (max-width:800px){
  body.auth header{padding:.7rem 1.2rem}
  body.auth header h1{font-size:1.4rem}
  body.app header h1{font-size:1.8rem}
  .page-title{font-size:1.5rem;letter-spacing:.14em}
  nav .links{justify-content:flex-start}
  td:first-child{font-size:1rem}
}
</style></head>
<body class="{{ 'app' if user else 'auth' }}">
<header>
  <h1>{{ store_name }}</h1>
  {% if user %}<nav>
    <div class="links">
      {# DSA QUEUE: the number in brackets on "Low Stock" is restock.size() #}
      {% for page, label in [('inventory','Inventory'),('sales','Record Sales'),('reports','Reports & Profit'),('search','Search'),('restock','Low Stock'),('history','History')] %}
      <a href="{{ url_for(page) }}"{% if request.endpoint == page %} class="on"{% endif %}>{{ label }}{% if page == 'restock' and restock_count %} ({{ restock_count }}){% endif %}</a>
      {% endfor %}
    </div>
    <div class="sp">
      {# DSA STACK: Undo Last = pop() the top of the history stack. Disabled when the stack isEmpty() #}
      <form method="post" action="{{ url_for('undo') }}" class="inline"><button {% if not undo_label %}disabled{% endif %} title="{{ undo_label or 'Nothing to undo' }}">Undo</button></form>
      <form method="post" action="{{ url_for('logout') }}" class="inline"><button>Log out</button></form>
    </div>
  </nav>{% endif %}
</header>
<main>
  {% for cat, msg in get_flashed_messages(with_categories=true) %}<div class="flash {{ cat }}">{{ msg }}</div>{% endfor %}
  {% block content %}{% endblock %}
</main>
<script>
function togglePwd(id, el) {
  const box = document.getElementById(id), hidden = box.type === "password";
  box.type = hidden ? "text" : "password";
  el.textContent = hidden ? "Hide" : "Show";
}
</script>
</body></html>""",
 
"login.html": """{% extends "base.html" %}{% from "macros.html" import field, pw %}
{% block content %}
<h2 class="auth-title">Login</h2>
<form method="post" class="auth-box">
  {{ field('Username', 'username', id='loginUser', required=true, autofocus=true, autocomplete='username') }}
  {{ pw('Password', 'password', 'loginPwd', 'current-password') }}
  <p class="auth-note">No account yet? <a href="{{ url_for('signup') }}">Sign up</a></p>
  <button class="submit">Log in</button>
</form>
{% endblock %}""",
 
"signup.html": """{% extends "base.html" %}{% from "macros.html" import field, pw %}
{% block content %}
<h2 class="auth-title">Create new Account</h2>
<form method="post" class="auth-box" onsubmit="confirmBox.value = signupPwd.value">
  {{ field('Username', 'username', id='signupUser', required=true, maxlength=20, autofocus=true, autocomplete='username') }}
  {{ field('Store’s Name', 'store', id='signupStore', required=true, maxlength=40, value='Gina Store', readonly=true) }}
  {{ pw('Password', 'password', 'signupPwd', 'new-password', minlength=4, maxlength=64) }}
  <input type="hidden" name="confirm" id="confirmBox">
  <p class="auth-note">Already have an account? <a href="{{ url_for('login') }}">Log in</a></p>
  <button class="submit">Sign up</button>
</form>
{% endblock %}""",
 
"error.html": """{% extends "base.html" %}
{% block content %}
<div class="card narrow"><h3>{{ title }}</h3><p>{{ text }}</p><p><a href="{{ url_for('inventory') }}">&larr; Back to inventory</a></p></div>
{% endblock %}""",
 
"inventory.html": """{% extends "base.html" %}{% from "macros.html" import card, stat, field %}
{% block content %}
<h2 class="page-title">Inventory</h2>
<div class="grid">{{ stat('Products', items|length) }}{{ stat('Stock Value', stock_value|peso) }}{{ stat('Low Stock Items', low_count) }}</div>
 
{% call card('Add New Products') %}
  {# DSA LIST ADT: this form calls insert() to add a new node to the linked list #}
  <form method="post" action="{{ url_for('addProduct') }}" class="row">
    {{ field('Product Name', 'name', box='flex:2;min-width:180px', required=true, maxlength=40) }}
    {{ field('Quantity', 'qty', 'number', box='flex:1;min-width:110px', min=0, required=true) }}
    {{ field('Capital Price', 'cost', 'number', box='flex:1;min-width:130px', min=0.01, step=0.01, required=true) }}
    {{ field('Selling Price', 'price', 'number', box='flex:1;min-width:130px', min=0.01, step=0.01, required=true) }}
    <button>Add Product</button>
  </form>
{% endcall %}
 
{% call card('Inventory List') %}
  {# DSA ARRAY: these links choose which selection sort is applied to the array #}
  <p class="sortline">Sort:{% for key, text in [('added','Added'),('name','Name'),('stock','Lowest Stock First')] %}{% if not loop.first %} &middot;{% endif %} <a href="{{ url_for('inventory', sort=key) }}"{% if sort == key %} class="on"{% endif %}>{{ text }}</a>{% endfor %}</p>
  {% if items %}<div class="scroll"><table>
    <tr><th>Product</th><th>Stock</th><th>Capital</th><th>Selling</th><th>Actions</th></tr>
    {% for p in items %}
    <tr{% if p.isLow() %} class="low"{% endif %}>
      <td>{{ p.name }}</td>
      <td>{{ p.qty }} {% if p.isLow() %}<span class="badge">Low</span>{% endif %}</td>
      <td>{{ p.cost|peso }}</td>
      <td>{{ p.price|peso }}</td>
      <td>
        <details><summary>Add Stock</summary>
          <form method="post" action="{{ url_for('addStock') }}" class="row"><input type="hidden" name="name" value="{{ p.name }}">
            <input name="qty" type="number" min="1" placeholder="Qty" required>
            <input name="cost" type="number" min="0.01" step="0.01" placeholder="Cost" value="{{ '%.2f'|format(p.cost) }}" required>
            <button class="sm">Add</button></form></details>
        <details><summary>Set Prices</summary>
          <form method="post" action="{{ url_for('updatePrice') }}" class="row"><input type="hidden" name="name" value="{{ p.name }}">
            <input name="cost" type="number" min="0.01" step="0.01" value="{{ '%.2f'|format(p.cost) }}" required>
            <input name="price" type="number" min="0.01" step="0.01" value="{{ '%.2f'|format(p.price) }}" required>
            <button class="sm">Save</button></form></details>
        {# DSA LIST ADT: Remove = search for the position, then removeAt(position) #}
        <form method="post" action="{{ url_for('removeProduct') }}" class="inline" onsubmit="return confirm('Remove this product?')"><input type="hidden" name="name" value="{{ p.name }}"><button class="danger sm">Remove</button></form>
      </td>
    </tr>
    {% endfor %}
  </table></div>
  {% else %}<p class="muted">No products yet. Add your first product above.</p>{% endif %}
{% endcall %}
{% endblock %}""",
 
"sales.html": """{% extends "base.html" %}{% from "macros.html" import card, field %}
{% block content %}
<h2 class="page-title">Record Sales</h2>
{% call card(style='padding-top:1.6rem') %}
  {% if products %}<form method="post" class="row">
    <div style="flex:2;min-width:220px"><label>Product Name</label>
      <select name="name" required>{% for p in products %}<option value="{{ p.name }}">{{ p.name }} ({{ p.qty }} in stock)</option>{% endfor %}</select></div>
    {{ field('Quantity Sold', 'qty', 'number', box='flex:1;min-width:140px', min=1, required=true) }}
    {{ field('Date', 'date', 'date', box='flex:1;min-width:190px', value=today, max=today, required=true) }}
    <button>Record Sale</button>
  </form>
  {% else %}<p class="muted">No products in stock to sell.</p>{% endif %}
{% endcall %}
{% call card('Recent Sales') %}
  {# DSA ARRAY: the last 10 items of the sales array, newest first #}
  {% if recent %}<div class="scroll"><table>
    <tr><th>Date</th><th>Product Name</th><th>Qty</th><th>Sales</th><th>Profit</th></tr>
    {% for s in recent %}<tr><td>{{ s.date }}</td><td>{{ s.name }}</td><td>{{ s.qty }}</td><td>{{ s.revenue|peso }}</td><td>{{ s.profit|peso }}</td></tr>{% endfor %}
  </table></div>
  {% else %}<p class="muted">No sales yet.</p>{% endif %}
{% endcall %}
{% endblock %}""",
 
"reports.html": """{% extends "base.html" %}{% from "macros.html" import card, stat, field, report_table %}
{% block content %}
<h2 class="page-title">Reports &amp; Profits</h2>
{# DSA ARRAY: every number on this page comes from ONE traversal of the sales array #}
{% call card('Overall: Capital, Sales & Profit') %}
  <div class="grid four" style="margin-bottom:0">
    {{ stat('Total Capital Spent', overall.capital|peso, 'outline') }}{{ stat('Total Sales', overall.revenue|peso, 'outline') }}
    {{ stat('Overall Profit', overall.profit|peso, 'outline') }}{{ stat('Stock Value (at cost)', overall.stock_value|peso, 'outline') }}
  </div>
{% endcall %}
{% call card('Daily Sales') %}
  <form method="get" class="row" style="margin-bottom:1.2rem">{{ field('Date', 'day', 'date', value=day) }}<button class="alt">View</button></form>
  <div class="grid" style="margin-bottom:0">{{ stat('Sales on ' ~ day, d.revenue|peso, 'outline') }}{{ stat('Profit', d.profit|peso, 'outline') }}{{ stat('Items Sold', d['items'], 'outline') }}</div>
{% endcall %}
{% call card('Monthly Sales') %}
  <form method="get" class="row" style="margin-bottom:1.2rem">{{ field('Month', 'month', 'month', value=month) }}<button class="alt">View</button></form>
  <div class="grid">{{ stat('Sales in ' ~ month, m.revenue|peso, 'outline') }}{{ stat('Profit', m.profit|peso, 'outline') }}{{ stat('Items Sold', m['items'], 'outline') }}</div>
  {{ report_table('Month', months, true) }}
{% endcall %}
{% call card('Daily Breakdown for ' ~ month) %}{{ report_table('Date', days) }}{% endcall %}
{% endblock %}""",
 
"search.html": """{% extends "base.html" %}{% from "macros.html" import card, field %}
{% block content %}
<h2 class="page-title">Search</h2>
{% call card('Search Products') %}
  {# DSA ARRAY: this keyword is checked against every product (linear search) #}
  <form method="get" class="row">{{ field('Keyword', 'q', box='flex:1;max-width:460px', value=q, maxlength=60, required=true, autofocus=true, placeholder='e.g. coke, datu puti, canton') }}<button>Search</button></form>
{% endcall %}
{% if found is not none %}{% call card('Results for “' ~ q ~ '” (' ~ found|length ~ ')') %}
  {% if found %}<div class="scroll"><table>
    <tr><th>Product</th><th>Stock</th><th>Capital</th><th>Selling</th></tr>
    {% for p in found %}<tr><td>{{ p.name }} {% if p.isLow() %}<span class="badge">Low</span>{% endif %}</td><td>{{ p.qty }}</td><td>{{ p.cost|peso }}</td><td>{{ p.price|peso }}</td></tr>{% endfor %}
  </table></div>
  {% else %}<p class="muted">No product matches “{{ q }}”.</p>{% endif %}
{% endcall %}{% endif %}
{% endblock %}""",
 
"restock.html": """{% extends "base.html" %}{% from "macros.html" import card, field %}
{% block content %}
<h2 class="page-title">Low-Stock Items</h2>
{% call card('Low-Stock Items') %}
  {# DSA QUEUE (FIFO): this list is the restock queue, FRONT first. The first item below is peek() #}
  {% if items %}<table><tr><th>#</th><th>Product Name</th><th>Stocks</th></tr>
  {% for p in items %}<tr><td>{{ loop.index }}</td><td>{{ p.name }}</td><td>{{ p.qty }}</td></tr>{% endfor %}</table>
  <p class="note">Restocking applies to the first item in the queue: {{ items[0].name }}</p>
  <form method="post" class="row">
    {{ field('Quantity Bought', 'qty', 'number', box='min-width:200px', min=1, required=true) }}
    {{ field('Cost Price', 'cost', 'number', box='min-width:200px', min=0.01, step=0.01, value='%.2f'|format(items[0].cost), required=true) }}
    <button>Restock Next Item</button>
  </form>
  {% else %}<p class="muted">All items are well stocked.</p>{% endif %}
{% endcall %}
{% endblock %}""",
 
"history.html": """{% extends "base.html" %}{% from "macros.html" import card %}
{% block content %}
<h2 class="page-title">History</h2>
{# DSA STACK (LIFO): newest action on top. The top entry is what Undo Last will reverse next #}
{% call card('Transaction History') %}
  {% if entries %}<ol class="log">{% for e in entries %}<li>{{ e }}</li>{% endfor %}</ol>{% else %}<p class="muted">No transactions yet.</p>{% endif %}
{% endcall %}
{% endblock %}""",
}
 
app.jinja_env.loader = DictLoader(TEMPLATES)
ensureDemo()
 
if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5000, debug=False)