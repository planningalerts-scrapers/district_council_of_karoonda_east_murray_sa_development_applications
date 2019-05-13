// Parses the development applications at the South Australian District Council of Karoonda East
// Murray web site and places them in a database.
//
// Michael Bone
// 12th February 2019
"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
const fs = require("fs");
const cheerio = require("cheerio");
const request = require("request-promise-native");
const sqlite3 = require("sqlite3");
const urlparser = require("url");
const moment = require("moment");
const pdfjs = require("pdfjs-dist");
const didyoumean2_1 = require("didyoumean2"), didyoumean = didyoumean2_1;
sqlite3.verbose();
const DevelopmentApplicationsUrl = "https://www.dckem.sa.gov.au/page.aspx?u=494";
const CommentUrl = "mailto:council@dckem.sa.gov.au";
// All valid street names, street suffixes, suburb names and hundred names.
let StreetNames = null;
let StreetSuffixes = null;
let SuburbNames = null;
let HundredNames = null;
// Sets up an sqlite database.
async function initializeDatabase() {
    return new Promise((resolve, reject) => {
        let database = new sqlite3.Database("data.sqlite");
        database.serialize(() => {
            database.run("create table if not exists [data] ([council_reference] text primary key, [address] text, [description] text, [info_url] text, [comment_url] text, [date_scraped] text, [date_received] text, [legal_description] text)");
            resolve(database);
        });
    });
}
// Inserts a row in the database if the row does not already exist.
async function insertRow(database, developmentApplication) {
    return new Promise((resolve, reject) => {
        let sqlStatement = database.prepare("insert or replace into [data] values (?, ?, ?, ?, ?, ?, ?, ?)");
        sqlStatement.run([
            developmentApplication.applicationNumber,
            developmentApplication.address,
            developmentApplication.description,
            developmentApplication.informationUrl,
            developmentApplication.commentUrl,
            developmentApplication.scrapeDate,
            developmentApplication.receivedDate,
            developmentApplication.legalDescription
        ], function (error, row) {
            if (error) {
                console.error(error);
                reject(error);
            }
            else {
                console.log(`    Saved application \"${developmentApplication.applicationNumber}\" with address \"${developmentApplication.address}\", description \"${developmentApplication.description}\", legal description \"${developmentApplication.legalDescription}\" and received date \"${developmentApplication.receivedDate}\" to the database.`);
                sqlStatement.finalize(); // releases any locks
                resolve(row);
            }
        });
    });
}
// Gets the highest Y co-ordinate of all elements that are considered to be in the same row as
// the specified element.  Take care to avoid extremely tall elements (because these may otherwise
// be considered as part of all rows and effectively force the return value of this function to
// the same value, regardless of the value of startElement).
function getRowTop(elements, startElement) {
    let top = startElement.y;
    for (let element of elements)
        if (element.y < startElement.y + startElement.height && element.y + element.height > startElement.y) // check for overlap
            if (getVerticalOverlapPercentage(startElement, element) > 50) // avoids extremely tall elements
                if (element.y < top)
                    top = element.y;
    return top;
}
// Constructs a rectangle based on the intersection of the two specified rectangles.
function intersect(rectangle1, rectangle2) {
    let x1 = Math.max(rectangle1.x, rectangle2.x);
    let y1 = Math.max(rectangle1.y, rectangle2.y);
    let x2 = Math.min(rectangle1.x + rectangle1.width, rectangle2.x + rectangle2.width);
    let y2 = Math.min(rectangle1.y + rectangle1.height, rectangle2.y + rectangle2.height);
    if (x2 >= x1 && y2 >= y1)
        return { x: x1, y: y1, width: x2 - x1, height: y2 - y1 };
    else
        return { x: 0, y: 0, width: 0, height: 0 };
}
// Calculates the square of the Euclidean distance between two elements.
function calculateDistance(element1, element2) {
    let point1 = { x: element1.x + element1.width, y: element1.y + element1.height / 2 };
    let point2 = { x: element2.x, y: element2.y + element2.height / 2 };
    if (point2.x < point1.x - element1.width / 5) // arbitrary overlap factor of 20% (ie. ignore elements that overlap too much in the horizontal direction)
        return Number.MAX_VALUE;
    return (point2.x - point1.x) * (point2.x - point1.x) + (point2.y - point1.y) * (point2.y - point1.y);
}
// Determines whether there is vertical overlap between two elements.
function isVerticalOverlap(element1, element2) {
    return element2.y < element1.y + element1.height && element2.y + element2.height > element1.y;
}
// Gets the percentage of vertical overlap between two elements (0 means no overlap and 100 means
// 100% overlap; and, for example, 20 means that 20% of the second element overlaps somewhere
// with the first element).
function getVerticalOverlapPercentage(element1, element2) {
    let y1 = Math.max(element1.y, element2.y);
    let y2 = Math.min(element1.y + element1.height, element2.y + element2.height);
    return (y2 < y1) ? 0 : (((y2 - y1) * 100) / element2.height);
}
// Gets the element immediately to the right of the specified element (but ignores elements that
// appear after a large horizontal gap).
function getRightElement(elements, element) {
    let closestElement = { text: undefined, x: Number.MAX_VALUE, y: Number.MAX_VALUE, width: 0, height: 0 };
    for (let rightElement of elements)
        if (isVerticalOverlap(element, rightElement) && // ensure that there is at least some vertical overlap
            getVerticalOverlapPercentage(element, rightElement) > 50 && // avoid extremely tall elements (ensure at least 50% overlap)
            (rightElement.x > element.x + element.width) && // ensure the element actually is to the right
            (rightElement.x - (element.x + element.width) < 30) && // avoid elements that appear after a large gap (arbitrarily ensure less than a 30 pixel gap horizontally)
            calculateDistance(element, rightElement) < calculateDistance(element, closestElement)) // check if closer than any element encountered so far
            closestElement = rightElement;
    return (closestElement.text === undefined) ? undefined : closestElement;
}
// Finds the element that most closely matches the specified text.
function findElement(elements, text, shouldSelectRightmostElement) {
    // Examine all the elements on the page that being with the same character as the requested
    // text.
    let condensedText = text.replace(/[\s,\-_]/g, "").toLowerCase();
    let firstCharacter = condensedText.charAt(0);
    let matches = [];
    for (let element of elements.filter(element => element.text.trim().toLowerCase().startsWith(firstCharacter))) {
        // Extract up to 5 elements to the right of the element that has text starting with the
        // required character (and so may be the start of the requested text).  Join together the
        // elements to the right in an attempt to find the best match to the text.
        let rightElement = element;
        let rightElements = [];
        do {
            rightElements.push(rightElement);
            let currentText = rightElements.map(element => element.text).join("").replace(/[\s,\-_]/g, "").toLowerCase();
            if (currentText.length > condensedText.length + 2) // stop once the text is too long
                break;
            if (currentText.length >= condensedText.length - 2) { // ignore until the text is close to long enough
                if (currentText === condensedText)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 0, text: currentText });
                else if (didyoumean2_1.default(currentText, [condensedText], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 1, text: currentText });
                else if (didyoumean2_1.default(currentText, [condensedText], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true }) !== null)
                    matches.push({ leftElement: rightElements[0], rightElement: rightElement, threshold: 2, text: currentText });
            }
            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5); // up to 5 elements
    }
    // Chose the best match (if any matches were found).  Note that trimming is performed here so
    // that text such as "  Plan" is matched in preference to text such as "plan)" (when looking
    // for elements that match "Plan").  For an example of this problem see "200/303/07" in
    // "https://www.walkerville.sa.gov.au/webdata/resources/files/DA%20Register%20-%202007.pdf".
    //
    // Note that if the match is made of several elements then sometimes the caller requires the
    // left most element and sometimes the right most element (depending on where further text
    // will be searched for relative to this "found" element).
    if (matches.length > 0) {
        let bestMatch = matches.reduce((previous, current) => (previous === undefined ||
            current.threshold < previous.threshold ||
            (current.threshold === previous.threshold && Math.abs(current.text.trim().length - condensedText.length) < Math.abs(previous.text.trim().length - condensedText.length)) ? current : previous), undefined);
        return shouldSelectRightmostElement ? bestMatch.rightElement : bestMatch.leftElement;
    }
    return undefined;
}
// Finds the start element of each development application on the current PDF page (there are
// typically one or two development applications on a single page and each development application
// typically begins with the text "Application No" or "Application Number").
function findStartElements(findText, elements) {
    // Examine all the elements on the page that begin with the same letter as the FindText.
    let startElements = [];
    for (let element of elements.filter(element => element.text.replace(/[^A-Za-z0-9\s]/g, "").toLowerCase().startsWith(findText.charAt(0).toLowerCase()))) {
        // Extract up to 5 elements to the right of the element that has text starting with the
        // first letter of the FindText (and so may be the start of the FindText).  Join together
        // the elements to the right in an attempt to find the best match to the FindText.
        let rightElement = element;
        let rightElements = [];
        let matches = [];
        do {
            rightElements.push(rightElement);
            // Allow for common miscellaneous characters such as " ", "." and "-".
            let text = rightElements.map(element => element.text).join("").replace(/[^A-Za-z0-9\s]/g, "").toLowerCase();
            if (text.length > findText.length + 2) // stop once the text is too long
                break;
            if (text.length >= findText.length - 2) { // ignore until the text is close to long enough
                if (text === findText.toLowerCase())
                    matches.push({ element: rightElement, threshold: 0, text: text });
                else if (didyoumean2_1.default(text, [findText], { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true }) !== null)
                    matches.push({ element: rightElement, threshold: 1, text: text });
            }
            rightElement = getRightElement(elements, rightElement);
        } while (rightElement !== undefined && rightElements.length < 5); // up to 5 elements
        // Choose the best match (if any matches were found).
        if (matches.length > 0) {
            let bestMatch = matches.reduce((previous, current) => (previous === undefined ||
                current.threshold < previous.threshold ||
                (current.threshold === previous.threshold && Math.abs(current.text.trim().length - findText.length) < Math.abs(previous.text.trim().length - findText.length)) ? current : previous), undefined);
            startElements.push(bestMatch.element);
        }
    }
    // Ensure the start elements are sorted in the order that they appear on the page.
    let yComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : 0);
    startElements.sort(yComparer);
    return startElements;
}
// Gets the text to the right in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.
function getRightText(elements, topLeftText, rightText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topLeftElement = findElement(elements, topLeftText, true);
    let rightElement = (rightText === undefined) ? undefined : findElement(elements, rightText, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false);
    if (topLeftElement === undefined)
        return undefined;
    let x = topLeftElement.x + topLeftElement.width;
    let y = topLeftElement.y;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;
    // Sort the elements by Y co-ordinate and then by X co-ordinate.
    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);
    // Join the elements into a single string.
    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Gets the text to the left in a rectangle, where the rectangle is delineated by the positions
// in which the three specified strings of (case sensitive) text are found.
function getLeftText(elements, topRightText, leftText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topRightElement = findElement(elements, topRightText, true);
    let leftElement = (leftText === undefined) ? undefined : findElement(elements, leftText, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false);
    if (topRightElement === undefined || leftElement === undefined || bottomElement === undefined)
        return undefined;
    let x = leftElement.x + leftElement.width;
    let y = topRightElement.y;
    let width = topRightElement.x - x;
    let height = bottomElement.y - y;
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;
    // Sort the elements by Y co-ordinate and then by X co-ordinate.
    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);
    // Join the elements into a single string.
    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Gets the text downwards in a rectangle, where the rectangle is delineated by the positions in
// which the three specified strings of (case sensitive) text are found.
function getDownText(elements, topText, leftText, rightText, bottomText) {
    // Construct a bounding rectangle in which the expected text should appear.  Any elements
    // over 50% within the bounding rectangle will be assumed to be part of the expected text.
    let topElement = findElement(elements, topText, true);
    let leftElement = findElement(elements, leftText, true);
    let rightElement = (rightText === undefined) ? undefined : findElement(elements, rightText, false);
    let bottomElement = (bottomText === undefined) ? undefined : findElement(elements, bottomText, false);
    if (topElement === undefined || leftElement === undefined)
        return undefined;
    let x = leftElement.x + leftElement.width;
    let y = topElement.y + topElement.height;
    let width = (rightElement === undefined) ? Number.MAX_VALUE : (rightElement.x - x);
    let height = (bottomElement === undefined) ? Number.MAX_VALUE : (bottomElement.y - y);
    let bounds = { x: x, y: y, width: width, height: height };
    // Gather together all elements that are at least 50% within the bounding rectangle.
    let intersectingElements = [];
    for (let element of elements) {
        let intersectingBounds = intersect(element, bounds);
        let intersectingArea = intersectingBounds.width * intersectingBounds.height;
        let elementArea = element.width * element.height;
        if (elementArea > 0 && intersectingArea * 2 > elementArea && element.text !== ":")
            intersectingElements.push(element);
    }
    if (intersectingElements.length === 0)
        return undefined;
    // Sort the elements by Y co-ordinate and then by X co-ordinate.
    let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
    intersectingElements.sort(elementComparer);
    // Join the elements into a single string.
    return intersectingElements.map(element => element.text).join(" ").trim().replace(/\s\s+/g, " ");
}
// Constructs the full address string based on the specified address components.
function oldFormatAddress(houseNumber, streetName, suburbName) {
    suburbName = suburbName.replace(/^HD /, "").replace(/ HD$/, "").replace(/ SA$/, "").trim();
    suburbName = SuburbNames[suburbName.toUpperCase()] || suburbName;
    let separator = ((houseNumber !== "" || streetName !== "") && suburbName !== "") ? ", " : "";
    return `${houseNumber} ${streetName}${separator}${suburbName}`.trim().replace(/\s\s+/g, " ").toUpperCase().replace(/\*/g, "");
}
// Parses the address from the house number, street name and suburb name.  Note that these
// address components may actually contain multiple addresses (delimited by "ü" characters).
function oldParseAddress(houseNumber, streetName, suburbName) {
    // Two or more addresses are sometimes recorded in the same field.  This is done in a way
    // which is ambiguous (ie. it is not possible to reconstruct the original addresses perfectly).
    //
    // For example, the following address:
    //
    //     House Number: ü35
    //           Street: RAILWAYüSCHOOL TCE SOUTHüTERRA
    //           Suburb: PASKEVILLEüPASKEVILLE
    //
    // should be interpreted as the following two addresses:
    //
    //     RAILWAY TCE SOUTH, PASKEVILLE
    //     35 SCHOOL TERRA(CE), PASKEVILLE
    //
    // whereas the following address:
    //
    //     House Number: 79ü4
    //           Street: ROSSLYNüSWIFT WINGS ROADüROAD
    //           Suburb: WALLAROOüWALLAROO
    //
    // should be interpreted as the following two addresses:
    //
    //     79 ROSSLYN ROAD, WALLAROO
    //     4 SWIFT WINGS ROAD, WALLAROO
    //
    // And so notice that in the first case above the "TCE" text of the Street belonged to the
    // first address.  Whereas in the second case above the "WINGS" text of the Street belonged
    // to the second address (this was deduced by examining actual existing street names).
    if (!houseNumber.includes("ü"))
        return oldFormatAddress(houseNumber, streetName, suburbName);
    // Split the house number on the "ü" character.
    let houseNumberTokens = houseNumber.split("ü");
    // Split the suburb name on the "ü" character.
    let suburbNameTokens = suburbName.split("ü");
    // The street name will have twice as many "ü" characters as the house number.  Each street
    // name is broken in two and the resulting strings are joined into two groups (delimited
    // by "ü" within the groups).  A single space is used to join the two groups together.
    //
    // For example, the street names "WALLACE STREET" and "MAY TERRACE" are broken in two as
    // "WALLACE" and "STREET"; and "MAY" and "TERRACE".  And then joined back together into
    // two groups, "WALLACEüMAY" and "STREETüTERRACE".  Those two groups are then concatenated
    // together using a single intervening space to form "WALLACEüMAY STREETüTERRACE".
    //
    // Unfortunately, the street name is truncated at 30 characters so some of the "ü" characters
    // may be missing.  Also note that there is an ambiguity in some cases as to whether a space
    // is a delimiter or is just a space that happens to occur within a street name or suffix
    // (such as "Kybunga Top" in "Kybunga Top Road" or "TERRACE SOUTH" in "RAILWAY TERRACE SOUTH").
    //
    // For example,
    //
    //     PHILLIPSüHARBISON ROADüROAD     <-- street names broken in two and joined into groups
    //     BarrüFrances StreetüTerrace     <-- street names broken in two and joined into groups
    //     GOYDERüGOYDERüMail HDüHDüRoad   <-- street names broken in two and joined into groups
    //     ORIENTALüWINDJAMMER COURTüCOUR  <-- truncated street suffix
    //     TAYLORüTAYLORüTAYLOR STREETüST  <-- missing "ü" character due to truncation
    //     EDGARüEASTüEAST STREETüTERRACE  <-- missing "ü" character due to truncation
    //     SOUTH WESTüSOUTH WEST TERRACEü  <-- missing "ü" character due to truncation
    //     ChristopherüChristopher Street  <-- missing "ü" character due to truncation
    //     PORT WAKEFIELDüPORT WAKEFIELD   <-- missing "ü" character due to truncation
    //     KENNETT STREETüKENNETT STREET   <-- missing "ü" character due to truncation (the missing text is probably " SOUTHüSOUTH")
    //     NORTH WESTüNORTH WESTüNORTH WE  <-- missing "ü" characters due to truncation
    //     RAILWAYüSCHOOL TCE SOUTHüTERRA  <-- ambiguous space delimiter
    //     BLYTHüWHITE WELL HDüROAD        <-- ambiguous space delimiter
    //     Kybunga TopüKybunga Top RoadüR  <-- ambiguous space delimiter
    //     SOUTHüSOUTH TERRACE EASTüTERRA  <-- ambiguous space delimiter
    // Artificially increase the street name tokens to twice the length (minus one) of the house
    // number tokens (this then simplifies the following processing).  The "minus one" is because
    // the middle token will be split in two later.
    let streetNameTokens = streetName.split("ü");
    while (streetNameTokens.length < 2 * houseNumberTokens.length - 1)
        streetNameTokens.push("");
    // Consider the following street name (however, realistically this would be truncated at
    // 30 characters; this is ignored for the sake of explaining the parsing),
    //
    //     Kybunga TopüSmithüRailway South RoadüTerrace EastüTerrace
    //
    // This street name would be split into the following tokens,
    //
    //     Token 0: Kybunga Top
    //     Token 1: Smith
    //     Token 2: Railway South Road  <-- the middle token contains a delimiting space (it is ambiguous as to which space is the correct delimiter)
    //     Token 3: Terrace East
    //     Token 4: Terrace
    //
    // And from these tokens, the following candidate sets of tokens would be constructed (each
    // broken into two groups).  Note that the middle token [Railway South Road] is broken into
    // two tokens in different ways depending on which space is chosen as the delimiter for the
    // groups: [Railway] and [South Road] or [Railway South] and [Road].
    //
    //     Candidate 1: [Kybunga Top] [Smith] [Railway]   [South Road] [Terrace East] [Terrace]
    //                 └───────────╴Group 1╶───────────┘ └──────────────╴Group 2╶──────────────┘
    //
    //     Candidate 2: [Kybunga Top] [Smith] [Railway South]   [Road] [Terrace East] [Terrace]
    //                 └──────────────╴Group 1╶──────────────┘ └───────────╴Group 2╶───────────┘
    let candidates = [];
    let middleTokenIndex = houseNumberTokens.length - 1;
    if (!streetNameTokens[middleTokenIndex].includes(" ")) // the space may be missing if the street name is truncated at 30 characters
        streetNameTokens[middleTokenIndex] += " "; // artificially add a space to simplify the processing
    let ambiguousTokens = streetNameTokens[middleTokenIndex].split(" ");
    for (let index = 1; index < ambiguousTokens.length; index++) {
        let group1 = [...streetNameTokens.slice(0, middleTokenIndex), ambiguousTokens.slice(0, index).join(" ")];
        let group2 = [ambiguousTokens.slice(index).join(" "), ...streetNameTokens.slice(middleTokenIndex + 1)];
        candidates.push({ group1: group1, group2: group2, hasInvalidHundredName: false });
    }
    // Full street names (with suffixes) can now be constructed for each candidate (by joining
    // together corresponding tokens from each group of tokens).
    let addresses = [];
    for (let candidate of candidates) {
        for (let index = 0; index < houseNumberTokens.length; index++) {
            // Expand street suffixes such as "Tce" to "TERRACE".
            let streetSuffix = candidate.group2[index].split(" ")
                .map(token => (StreetSuffixes[token.toUpperCase()] === undefined) ? token : StreetSuffixes[token.toUpperCase()])
                .join(" ");
            // Construct the full street name (including the street suffix).
            let houseNumber = houseNumberTokens[index];
            let streetName = (candidate.group1[index] + " " + streetSuffix).trim().replace(/\s\s+/g, " ");
            if (streetName === "")
                continue; // ignore blank street names
            // Check whether the street name is actually a hundred name such as "BARUNGA HD".
            if (streetName.endsWith(" HD") || streetName.toUpperCase().endsWith(" HUNDRED")) { // very likely a hundred name
                let hundredNameMatch = didyoumean2_1.default(streetName.slice(0, -3), HundredNames, { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 0, trimSpaces: true });
                if (hundredNameMatch === null)
                    candidate.hasInvalidHundredName = true; // remember that there is an invalid hundred name (for example, "BARUNGA View HD")
                continue; // ignore all hundred names names
            }
            // Determine the associated suburb name.
            let associatedSuburbName = suburbNameTokens[index];
            if (associatedSuburbName === undefined || associatedSuburbName.trim() === "")
                continue; // ignore blank suburb names
            // Choose the best matching street name (from the known street names).
            let streetNameMatch = didyoumean2_1.default(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 0, trimSpaces: true });
            if (streetNameMatch !== null)
                addresses.push({ houseNumber: houseNumber, streetName: streetName, suburbName: associatedSuburbName, threshold: 0, candidate: candidate });
            else {
                streetNameMatch = didyoumean2_1.default(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
                if (streetNameMatch !== null)
                    addresses.push({ houseNumber: houseNumber, streetName: streetNameMatch, suburbName: associatedSuburbName, threshold: 1, candidate: candidate });
                else {
                    streetNameMatch = didyoumean2_1.default(streetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 2, trimSpaces: true });
                    if (streetNameMatch !== null)
                        addresses.push({ houseNumber: houseNumber, streetName: streetNameMatch, suburbName: associatedSuburbName, threshold: 2, candidate: candidate });
                    else
                        addresses.push({ houseNumber: houseNumber, streetName: streetName, suburbName: associatedSuburbName, threshold: Number.MAX_VALUE, candidate: candidate }); // unrecognised street name
                }
            }
        }
    }
    if (addresses.length === 0)
        return undefined; // no valid addresses found
    // Sort the addresses so that "better" addresses are moved to the front of the array.
    addresses.sort(addressComparer);
    // Format and return the "best" address.
    let address = addresses[0];
    return oldFormatAddress(address.houseNumber, address.streetName, address.suburbName);
}
// Returns a number indicating which address is "larger" (in this case "larger" means a "worse"
// address).  This can be used to sort addresses so that "better" addresses, ie. those with a
// house number and fewer spelling errors appear at the start of an array.
function addressComparer(a, b) {
    // As long as there are one or two spelling errors then prefer the address with a
    // house number (even if it has more spelling errors).
    if (a.threshold <= 2 && b.threshold <= 2) {
        if (a.houseNumber === "" && b.houseNumber !== "")
            return 1;
        else if (a.houseNumber !== "" && b.houseNumber === "")
            return -1;
    }
    // For larger numbers of spelling errors prefer addresses with fewer spelling errors before
    // considering the presence of a house number.
    if (a.threshold > b.threshold)
        return 1;
    else if (a.threshold < b.threshold)
        return -1;
    if (a.houseNumber === "" && b.houseNumber !== "")
        return 1;
    else if (a.houseNumber !== "" && b.houseNumber === "")
        return -1;
    // All other things being equal (as tested above), avoid addresses belonging to a candidate
    // that has an invalid hundred name.  This is because having an invalid hundred name often
    // means that the wrong delimiting space has been chosen for that candidate (as below where
    // candidate 0 contains the invalid hundred name, "BARUNGA View HD", and so likely the other
    // address in that candidate is also wrong, namely, "Lake Road").
    //
    // Where there are multiple candidates mark down the candidates that contain street names
    // ending in " HD" and so likely represent a hundred name, but do not actually contain a
    // valid hundred name.  For example, the valid street name "Lake View Road" in candidate 1
    // is the better choice in the following because the hundred name "BARUNGA View HD" in
    // candidate 0 is invalid.
    //
    //     BARUNGAüLake View HDüRoad
    //
    // Candidate 0: [BARUNGA] [Lake]   [View HD] [Road]
    //             └───╴Group 1╶────┘ └───╴Group 2╶────┘
    //     Resulting street names:
    //         BARUNGA View HD  <-- invalid hundred name
    //         Lake Road        <-- valid street name
    //
    // Candidate 1: [BARUNGA] [Lake View]   [HD] [Road]
    //             └──────╴Group 1╶──────┘ └─╴Group 2╶─┘
    //     Resulting street names:
    //         BARUNGA HD      <-- valid hundred name
    //         Lake View Road  <-- valid street name
    if (a.candidate.hasInvalidHundredName && !b.candidate.hasInvalidHundredName)
        return 1;
    else if (!a.candidate.hasInvalidHundredName && b.candidate.hasInvalidHundredName)
        return -1;
}
// Parses the details from the elements associated with a single development application.
function oldParseApplicationElements(elements, startElement, informationUrl) {
    // Get the application number.
    let applicationNumber = getRightText(elements, "Application No", "Application Date", "Applicants Name");
    if (applicationNumber === undefined || applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    applicationNumber = applicationNumber.replace(/[Il,]/g, "/");
    console.log(`    Found \"${applicationNumber}\".`);
    // Get the received date.
    let receivedDateText = "";
    if (elements.some(element => element.text.trim() === "Application Received")) {
        receivedDateText = getRightText(elements, "Application Received", "Planning Approval", "Land Division Approval");
        if (receivedDateText === undefined)
            receivedDateText = getRightText(elements, "Application Date", "Planning Approval", "Application Received");
    }
    else if (elements.some(element => element.text.trim() === "Application received")) {
        receivedDateText = getRightText(elements, "Application received", "Planning Approval", "Land Division Approval");
        if (receivedDateText === undefined)
            receivedDateText = getRightText(elements, "Application Date", "Planning Approval", "Application received");
    }
    else if (elements.some(element => element.text.trim() === "Building Approval")) {
        receivedDateText = getLeftText(elements, "Building Approval", "Application Date", "Building  received");
        if (receivedDateText === undefined)
            receivedDateText = getRightText(elements, "Application Date", "Planning Approval", "Building Approval");
    }
    let receivedDate = undefined;
    if (receivedDateText !== undefined)
        receivedDate = moment(receivedDateText.trim(), ["D/MM/YYYY", "D/MM/YY"], true);
    // Get the house number, street and suburb of the address.
    let houseNumber = getRightText(elements, "Property House No", "Planning Conditions", "Lot");
    if (houseNumber === undefined || houseNumber === "0")
        houseNumber = "";
    let streetName = getRightText(elements, "Property street", "Planning Conditions", "Property suburb");
    if (streetName === undefined || streetName === "" || streetName === "0") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because an address was not found or parsed (there is no street name).  Elements: ${elementSummary}`);
        return undefined;
    }
    let suburbName = getRightText(elements, "Property suburb", "Planning Conditions", "Title");
    if (suburbName === undefined || suburbName === "" || suburbName === "0") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because an address was not found or parsed (there is no suburb name for street \"${streetName}\").  Elements: ${elementSummary}`);
        return undefined;
    }
    let address = oldParseAddress(houseNumber, streetName, suburbName);
    if (address === undefined) {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because an address was not parsed from the house number \"${houseNumber}\", street name \"${streetName}\" and suburb name \"${suburbName}\".  Elements: ${elementSummary}`);
        return undefined;
    }
    // Get the legal description.
    let legalElements = [];
    let lot = getRightText(elements, "Lot", "Planning Conditions", "Section");
    if (lot !== undefined)
        legalElements.push(`Lot ${lot}`);
    let section = getRightText(elements, "Section", "Planning Conditions", "Plan");
    if (section !== undefined)
        legalElements.push(`Section ${section}`);
    let plan = getRightText(elements, "Plan", "Planning Conditions", "Property Street");
    if (plan !== undefined)
        legalElements.push(`Plan ${plan}`);
    let title = getRightText(elements, "Title", "Planning Conditions", "Hundred");
    if (title !== undefined)
        legalElements.push(`Title ${title}`);
    let hundred = getRightText(elements, "Hundred", "Planning Conditions", "Development Description");
    if (hundred !== undefined)
        legalElements.push(`Hundred ${hundred}`);
    let legalDescription = legalElements.join(", ");
    // Get the description.
    let description = getDownText(elements, "Hundred", "Development Description", "Relevant Authority Referred to", "class");
    // Construct the resulting application information.
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description !== undefined && description.trim() !== "") ? description : "No Description Provided"),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : "",
        legalDescription: legalDescription
    };
}
// Formats (and corrects) an address.
function newFormatAddress(applicationNumber, address) {
    address = address.trim().replace(/[-–]+$/, "").replace(/\s\s+/g, " ").trim(); // remove trailing dashes and multiple white space characters
    if (address.replace(/[\s,0-]/g, "") === "" || address.startsWith("No Residential Address")) // ignores addresses such as "0 0, 0" and "-"
        return "";
    // Remove the comma in house numbers larger than 1000.  For example, the following addresses:
    //
    //     4,665 Princes HWY MENINGIE 5264
    //     11,287 Princes HWY SALT CREEK 5264
    //
    // would be converted to the following:
    //
    //     4665 Princes HWY MENINGIE 5264
    //     11287 Princes HWY SALT CREEK 5264
    if (/^\d,\d\d\d/.test(address))
        address = address.substring(0, 1) + address.substring(2);
    else if (/^\d\d,\d\d\d/.test(address))
        address = address.substring(0, 2) + address.substring(3);
    let tokens = address.split(" ");
    let postCode = undefined;
    let token = tokens.pop();
    if (token === undefined)
        return address;
    if (/^\d\d\d\d$/.test(token))
        postCode = token;
    else
        tokens.push(token);
    // Ensure that a state code is added before the post code if a state code is not present.
    let state = "SA";
    token = tokens.pop();
    if (token === undefined)
        return address;
    if (["ACT", "NSW", "NT", "QLD", "SA", "TAS", "VIC", "WA"].includes(token.toUpperCase()))
        state = token.toUpperCase();
    else
        tokens.push(token);
    // Construct a fallback address to be used if the suburb name cannot be determined later.
    let fallbackAddress = (postCode === undefined) ? address : [...tokens, state, postCode].join(" ").trim();
    // Pop tokens from the end of the array until a valid suburb name is encountered (allowing
    // for a few spelling errors).  Note that this starts by examining for longer matches
    // (consisting of four tokens) before examining shorter matches.  This approach ensures
    // that the following address:
    //
    //     2,800 Woods Well RD COLEBATCH 5266
    //
    // is correctly converted to the following address:
    //
    //     2800 WOODS WELL ROAD, COLEBATCH SA 5266
    //
    // rather than (incorrectly) to the following address (notice that the street name has "BELL"
    // instead of "WELL" because there actually is a street named "BELL ROAD").
    //
    //     2800 Woods BELL ROAD, COLEBATCH SA 5266
    let suburbName = undefined;
    for (let index = 4; index >= 1; index--) {
        let trySuburbName = tokens.slice(-index).join(" ");
        let suburbNameMatch = didyoumean2_1.default(trySuburbName, Object.keys(SuburbNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
        if (suburbNameMatch !== null) {
            suburbName = SuburbNames[suburbNameMatch];
            tokens.splice(-index, index); // remove elements from the end of the array           
            break;
        }
    }
    // Expand any street suffix (for example, this converts "ST" to "STREET").
    token = tokens.pop();
    if (token !== undefined) {
        token = token.trim().replace(/,+$/, "").trim(); // removes trailing commas
        let streetSuffix = StreetSuffixes[token.toUpperCase()];
        if (streetSuffix === undefined)
            streetSuffix = Object.values(StreetSuffixes).find(streetSuffix => streetSuffix === token.toUpperCase()); // the street suffix is already expanded
        if (streetSuffix === undefined)
            tokens.push(token); // unrecognised street suffix
        else
            tokens.push(streetSuffix); // add back the expanded street suffix
    }
    // Pop tokens from the end of the array until a valid street name is encountered (allowing
    // for a few spelling errors).  Similar to the examination of suburb names, this examines
    // longer matches before examining shorter matches (for the same reason).
    let streetName = undefined;
    for (let index = 5; index >= 1; index--) {
        let tryStreetName = tokens.slice(-index).join(" ").trim().replace(/,+$/, "").trim(); // allows for commas after the street name
        let streetNameMatch = didyoumean2_1.default(tryStreetName, Object.keys(StreetNames), { caseSensitive: false, returnType: didyoumean.ReturnTypeEnums.FIRST_CLOSEST_MATCH, thresholdType: didyoumean.ThresholdTypeEnums.EDIT_DISTANCE, threshold: 1, trimSpaces: true });
        if (streetNameMatch !== null) {
            streetName = streetNameMatch;
            let suburbNames = StreetNames[streetNameMatch];
            tokens.splice(-index, index); // remove elements from the end of the array           
            // If the suburb was not determined earlier then attempt to obtain the suburb based
            // on the street (ie. if there is only one suburb associated with the street).  For
            // example, this would automatically add the suburb to "22 Jefferson CT 5263",
            // producing the address "22 JEFFERSON COURT, WELLINGTON EAST SA 5263".
            if (suburbName === undefined && suburbNames.length === 1)
                suburbName = SuburbNames[suburbNames[0]];
            break;
        }
    }
    // If a post code was included in the original address then use it to override the post code
    // included in the suburb name (because the post code in the original address is more likely
    // to be correct).
    if (postCode !== undefined && suburbName !== undefined)
        suburbName = suburbName.replace(/\s+\d\d\d\d$/, " " + postCode);
    // Do not allow an address that does not have a suburb name.
    if (suburbName === undefined) {
        console.log(`Ignoring the development application "${applicationNumber}" because a suburb name could not be determined for the address: ${address}`);
        return "";
    }
    // Reconstruct the address with a comma between the street address and the suburb.
    if (suburbName === undefined || suburbName.trim() === "")
        address = fallbackAddress;
    else {
        if (streetName !== undefined && streetName.trim() !== "")
            tokens.push(streetName);
        let streetAddress = tokens.join(" ").trim().replace(/,+$/, "").trim(); // removes trailing commas
        address = streetAddress + (streetAddress === "" ? "" : ", ") + suburbName;
    }
    // Ensure that the address includes the state "SA".
    if (address !== "" && !/\bSA\b/g.test(address))
        address += " SA";
    return address;
}
// Parses the details from the elements associated with a single development application.
function newParseApplicationElements(elements, startElement, informationUrl) {
    // Get the application number.
    let applicationNumber = getRightText(elements, "Application Number", "Application Date", "Assessment Number");
    if (applicationNumber === undefined || applicationNumber === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Could not find the application number on the PDF page for the current development application.  The development application will be ignored.  Elements: ${elementSummary}`);
        return undefined;
    }
    applicationNumber = applicationNumber.replace(/[Il,]/g, "/");
    console.log(`    Found \"${applicationNumber}\".`);
    // Get the received date.
    let receivedDateText = getRightText(elements, "Application Date", "Development Completed", "Planning Lodged");
    let receivedDate = undefined;
    if (receivedDateText !== undefined)
        receivedDate = moment(receivedDateText.trim(), ["D/MM/YYYY", "D/MM/YY"], true);
    // Get the house number, street and suburb of the address.
    let address = getRightText(elements, "Property Address", "Application Fees", "Development Description");
    if (address !== undefined)
        address = newFormatAddress(applicationNumber, address.replace(/\bAustralia$/gi, "").trim());
    if (address === undefined || address === "") {
        let elementSummary = elements.map(element => `[${element.text}]`).join("");
        console.log(`Application number ${applicationNumber} will be ignored because an address was not found.  Elements: ${elementSummary}`);
        return undefined;
    }
    // Get the description.
    let description = getRightText(elements, "Development Description", "Application Fees", "Relevant Authority");
    // Construct the resulting application information.
    return {
        applicationNumber: applicationNumber,
        address: address,
        description: ((description !== undefined && description.trim() !== "") ? description : "No Description Provided"),
        informationUrl: informationUrl,
        commentUrl: CommentUrl,
        scrapeDate: moment().format("YYYY-MM-DD"),
        receivedDate: (receivedDate !== undefined && receivedDate.isValid()) ? receivedDate.format("YYYY-MM-DD") : "",
        legalDescription: ""
    };
}
// Parses the development applications in the specified date range.
async function parsePdf(url) {
    console.log(`Reading development applications from ${url}.`);
    let developmentApplications = [];
    // Read the PDF.
    let buffer = await request({ url: url, encoding: null, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    // Parse the PDF.  Each page has the details of multiple applications.  Note that the PDF is
    // re-parsed on each iteration of the loop (ie. once for each page).  This then avoids large
    // memory usage by the PDF (just calling page._destroy() on each iteration of the loop appears
    // not to be enough to release all memory used by the PDF parsing).
    for (let pageIndex = 0; pageIndex < 500; pageIndex++) { // limit to an arbitrarily large number of pages (to avoid any chance of an infinite loop)
        let pdf = await pdfjs.getDocument({ data: buffer, disableFontFace: true, ignoreErrors: true });
        if (pageIndex >= pdf.numPages)
            break;
        console.log(`Reading and parsing applications from page ${pageIndex + 1} of ${pdf.numPages}.`);
        let page = await pdf.getPage(pageIndex + 1);
        let textContent = await page.getTextContent();
        let viewport = await page.getViewport(1.0);
        let elements = textContent.items.map(item => {
            let transform = pdfjs.Util.transform(viewport.transform, item.transform);
            // Work around the issue https://github.com/mozilla/pdf.js/issues/8276 (heights are
            // exaggerated).  The problem seems to be that the height value is too large in some
            // PDFs.  Provide an alternative, more accurate height value by using a calculation
            // based on the transform matrix.
            let workaroundHeight = Math.sqrt(transform[2] * transform[2] + transform[3] * transform[3]);
            return { text: item.str, x: transform[4], y: transform[5], width: item.width, height: workaroundHeight };
        });
        // Release the memory used by the PDF now that it is no longer required (it will be
        // re-parsed on the next iteration of the loop for the next page).
        await pdf.destroy();
        if (global.gc)
            global.gc();
        // Sort the elements by Y co-ordinate and then by X co-ordinate.
        let elementComparer = (a, b) => (a.y > b.y) ? 1 : ((a.y < b.y) ? -1 : ((a.x > b.x) ? 1 : ((a.x < b.x) ? -1 : 0)));
        elements.sort(elementComparer);
        // Group the elements into sections based on where the application number text starts.
        let applicationElementGroups = [];
        let startElements = findStartElements("ApplicationNo", elements);
        if (startElements.length === 0)
            startElements = findStartElements("ApplicationNumber", elements);
        for (let index = 0; index < startElements.length; index++) {
            // Determine the highest Y co-ordinate of this row and the next row (or the bottom of
            // the current page).  Allow some leeway vertically (add some extra height) because
            // in some cases the lodged date might be higher up than the "Application No" or
            // "Application Number" text.
            let startElement = startElements[index];
            let raisedStartElement = {
                text: startElement.text,
                x: startElement.x,
                y: startElement.y - startElement.height / 2,
                width: startElement.width,
                height: startElement.height
            };
            let rowTop = getRowTop(elements, raisedStartElement);
            let nextRowTop = (index + 1 < startElements.length) ? getRowTop(elements, startElements[index + 1]) : Number.MAX_VALUE;
            // Extract all elements between the two rows.
            applicationElementGroups.push({ startElement: startElements[index], elements: elements.filter(element => element.y >= rowTop && element.y + element.height < nextRowTop) });
        }
        // Parse the development application from each group of elements (ie. a section of the
        // current page of the PDF document).  If the same application number is encountered a
        // second time in the same document then this likely indicates the parsing has incorrectly
        // recognised some of the digits in the application number.  In this case add a suffix to
        // the application number so it is unique (and so will be inserted into the database later
        // instead of being ignored).
        for (let applicationElementGroup of applicationElementGroups) {
            let developmentApplication;
            if (applicationElementGroup.startElement.text.toLowerCase().trim() === "application no")
                developmentApplication = oldParseApplicationElements(applicationElementGroup.elements, applicationElementGroup.startElement, url);
            else
                developmentApplication = newParseApplicationElements(applicationElementGroup.elements, applicationElementGroup.startElement, url);
            if (developmentApplication !== undefined) {
                let suffix = 0;
                let applicationNumber = developmentApplication.applicationNumber;
                while (developmentApplications.some(otherDevelopmentApplication => otherDevelopmentApplication.applicationNumber === developmentApplication.applicationNumber))
                    developmentApplication.applicationNumber = `${applicationNumber} (${++suffix})`; // add a unique suffix
                developmentApplications.push(developmentApplication);
            }
        }
    }
    return developmentApplications;
}
// Gets a random integer in the specified range: [minimum, maximum).
function getRandom(minimum, maximum) {
    return Math.floor(Math.random() * (Math.floor(maximum) - Math.ceil(minimum))) + Math.ceil(minimum);
}
// Pauses for the specified number of milliseconds.
function sleep(milliseconds) {
    return new Promise(resolve => setTimeout(resolve, milliseconds));
}
// Parses the development applications.
async function main() {
    // Ensure that the database exists.
    let database = await initializeDatabase();
    // Read the files containing all possible street names, street suffixes, suburb names and
    // hundred names.
    StreetNames = {};
    for (let line of fs.readFileSync("streetnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetNameTokens = line.toUpperCase().split(",");
        let streetName = streetNameTokens[0].trim();
        let suburbName = streetNameTokens[1].trim();
        (StreetNames[streetName] || (StreetNames[streetName] = [])).push(suburbName); // several suburbs may exist for the same street name
    }
    StreetSuffixes = {};
    for (let line of fs.readFileSync("streetsuffixes.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let streetSuffixTokens = line.toUpperCase().split(",");
        StreetSuffixes[streetSuffixTokens[0].trim()] = streetSuffixTokens[1].trim();
    }
    SuburbNames = {};
    for (let line of fs.readFileSync("suburbnames.txt").toString().replace(/\r/g, "").trim().split("\n")) {
        let suburbTokens = line.toUpperCase().split(",");
        SuburbNames[suburbTokens[0].trim()] = suburbTokens[1].trim();
    }
    HundredNames = [];
    for (let line of fs.readFileSync("hundrednames.txt").toString().replace(/\r/g, "").trim().split("\n"))
        HundredNames.push(line.trim().toUpperCase());
    // Read the main page of development applications.
    console.log(`Retrieving page: ${DevelopmentApplicationsUrl}`);
    let body = await request({ url: DevelopmentApplicationsUrl, rejectUnauthorized: false, proxy: process.env.MORPH_PROXY });
    await sleep(2000 + getRandom(0, 5) * 1000);
    let $ = cheerio.load(body);
    let pdfUrls = [];
    for (let element of $("div.uFileItem p a").get()) {
        let pdfUrl = new urlparser.URL(element.attribs.href, DevelopmentApplicationsUrl).href;
        if (pdfUrl.toLowerCase().includes("register") && !pdfUrl.toLowerCase().includes("members") && pdfUrl.toLowerCase().includes(".pdf"))
            if (!pdfUrls.some(url => url === pdfUrl))
                pdfUrls.push(pdfUrl);
    }
    // Always parse the most recent PDF file and randomly select one other PDF file to parse.
    if (pdfUrls.length === 0) {
        console.log("No PDF files were found on the page.");
        return;
    }
    console.log(`Found ${pdfUrls.length} PDF file(s).  Selecting two to parse.`);
    // Select the most recent PDF.  And randomly select one other PDF (avoid processing all PDFs
    // at once because this may use too much memory, resulting in morph.io terminating the current
    // process).
    let selectedPdfUrls = [];
    selectedPdfUrls.push(pdfUrls.shift());
    if (pdfUrls.length > 0)
        selectedPdfUrls.push(pdfUrls[getRandom(0, pdfUrls.length)]);
    if (getRandom(0, 2) === 0)
        selectedPdfUrls.reverse();
    for (let pdfUrl of selectedPdfUrls) {
        console.log(`Parsing document: ${pdfUrl}`);
        let developmentApplications = await parsePdf(pdfUrl);
        console.log(`Parsed ${developmentApplications.length} development application(s) from document: ${pdfUrl}`);
        // Attempt to avoid reaching 512 MB memory usage (this will otherwise result in the
        // current process being terminated by morph.io).
        if (global.gc)
            global.gc();
        console.log(`Saving development applications to the database.`);
        for (let developmentApplication of developmentApplications)
            await insertRow(database, developmentApplication);
    }
}
main().then(() => console.log("Complete.")).catch(error => console.error(error));
//# sourceMappingURL=data:application/json;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoic2NyYXBlci5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzIjpbInNjcmFwZXIudHMiXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6IkFBQUEsZ0dBQWdHO0FBQ2hHLGlEQUFpRDtBQUNqRCxFQUFFO0FBQ0YsZUFBZTtBQUNmLHFCQUFxQjtBQUVyQixZQUFZLENBQUM7O0FBRWIseUJBQXlCO0FBQ3pCLG1DQUFtQztBQUNuQyxrREFBa0Q7QUFDbEQsbUNBQW1DO0FBQ25DLGlDQUFpQztBQUNqQyxpQ0FBaUM7QUFDakMsb0NBQW9DO0FBQ3BDLHlFQUFzRDtBQUV0RCxPQUFPLENBQUMsT0FBTyxFQUFFLENBQUM7QUFFbEIsTUFBTSwwQkFBMEIsR0FBRyw2Q0FBNkMsQ0FBQztBQUNqRixNQUFNLFVBQVUsR0FBRyxnQ0FBZ0MsQ0FBQztBQUlwRCwyRUFBMkU7QUFFM0UsSUFBSSxXQUFXLEdBQUcsSUFBSSxDQUFDO0FBQ3ZCLElBQUksY0FBYyxHQUFHLElBQUksQ0FBQztBQUMxQixJQUFJLFdBQVcsR0FBRyxJQUFJLENBQUM7QUFDdkIsSUFBSSxZQUFZLEdBQUcsSUFBSSxDQUFDO0FBRXhCLDhCQUE4QjtBQUU5QixLQUFLLFVBQVUsa0JBQWtCO0lBQzdCLE9BQU8sSUFBSSxPQUFPLENBQUMsQ0FBQyxPQUFPLEVBQUUsTUFBTSxFQUFFLEVBQUU7UUFDbkMsSUFBSSxRQUFRLEdBQUcsSUFBSSxPQUFPLENBQUMsUUFBUSxDQUFDLGFBQWEsQ0FBQyxDQUFDO1FBQ25ELFFBQVEsQ0FBQyxTQUFTLENBQUMsR0FBRyxFQUFFO1lBQ3BCLFFBQVEsQ0FBQyxHQUFHLENBQUMsd05BQXdOLENBQUMsQ0FBQztZQUN2TyxPQUFPLENBQUMsUUFBUSxDQUFDLENBQUM7UUFDdEIsQ0FBQyxDQUFDLENBQUM7SUFDUCxDQUFDLENBQUMsQ0FBQztBQUNQLENBQUM7QUFFRCxtRUFBbUU7QUFFbkUsS0FBSyxVQUFVLFNBQVMsQ0FBQyxRQUFRLEVBQUUsc0JBQXNCO0lBQ3JELE9BQU8sSUFBSSxPQUFP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
